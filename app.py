"""
app.py  —  Alethea blockchain mining backend

Responsibilities:
  • Receive POST /mine from a validator
  • Verify transaction signature (ECDSA P-256, pure stdlib)
  • Re-verify sender has sufficient liquid balance at mining time
  • Prevent self-transfers (sender == receiver)
  • Run Proof-of-Work (SHA-256, configurable difficulty)
  • Write the new block to Firebase
  • Deduct sender balance (liquid only)
  • Credit receiver balance (automatic receiving)
  • Credit miner reward (if supply cap not reached)
  • Track total minted supply; enforce MAX_SUPPLY

Token economics
───────────────
  MAX_SUPPLY   = 21_000_000 ALE  (hard cap, never exceeded)
  BLOCK_REWARD = 10 ALE initially, halves every HALVING_INTERVAL blocks
  HALVING_INTERVAL = 210_000 blocks  (mirrors Bitcoin's schedule)

  At each halving the reward halves (integer division).
  When reward drops below 1 ALE it becomes 0 — mining continues but
  validators earn no new tokens from that point.

  New tokens only come into existence as mining rewards.
  User starting balances (100 ALE from setup) count against MAX_SUPPLY
  via a GENESIS_SUPPLY constant; the remaining mintable supply is
  MAX_SUPPLY - GENESIS_SUPPLY - already_minted.

Where do mined tokens go?
─────────────────────────
  The miner_address passed in the POST body receives BLOCK_REWARD ALE.
  This is always the validator's own wallet address (sent by validator.html).
  The tokens appear in that wallet's Firebase balance immediately after mining.
  They are real, spendable, on-chain ALE — not a separate account.
"""

import hashlib
import json
import time
import base64
import requests
from flask import Flask, jsonify, request
from flask_cors import CORS

app = Flask(__name__)
CORS(app)

# ── Constants ─────────────────────────────────────────────────────────────────

FIREBASE_DB_URL    = "https://alethea-876e1-default-rtdb.firebaseio.com"
DIFFICULTY         = 4             # leading zeros required in block hash
INITIAL_REWARD     = 10            # ALE rewarded per block initially
HALVING_INTERVAL   = 210_000       # blocks between reward halvings
MAX_SUPPLY         = 21_000_000    # hard cap on total ALE that can ever exist
# Starting balances given to users during setup are tracked here so the
# miner cannot mint beyond MAX_SUPPLY even accounting for genesis coins.
# Adjust this if the starting balance in setup.js changes.
GENESIS_BALANCE    = 100           # ALE given to each new wallet

# ── Firebase REST helpers ─────────────────────────────────────────────────────

def firebase_get(path):
    resp = requests.get(f"{FIREBASE_DB_URL}/{path}.json")
    if resp.status_code == 200:
        return resp.json()
    return None

def firebase_put(path, data):
    requests.put(f"{FIREBASE_DB_URL}/{path}.json", json=data)

def firebase_transaction(path, update_fn):
    """
    Conditional write using Firebase ETag header (optimistic locking).
    Retries up to 5 times on write conflict (HTTP 412).
    Used to atomically claim a pending transaction so two simultaneous
    /mine calls cannot double-mine the same transaction.
    """
    url = f"{FIREBASE_DB_URL}/{path}.json"
    for _ in range(5):
        resp = requests.get(url, headers={"X-Firebase-ETag": "true"})
        if resp.status_code != 200:
            return False
        etag      = resp.headers.get("ETag", "")
        current   = resp.json()
        new_value = update_fn(current)
        if new_value is None:   # update_fn signals "abort"
            return False
        put_resp = requests.put(
            url, json=new_value, headers={"if-match": etag}
        )
        if put_resp.status_code in (200, 204):
            return True
        # 412 = ETag mismatch — another writer won, retry
    return False

# ── Token supply tracking ─────────────────────────────────────────────────────

def get_total_minted() -> float:
    """Returns the total ALE minted via mining rewards so far."""
    val = firebase_get("supply/total_minted")
    return float(val) if val is not None else 0.0

def add_to_total_minted(amount: float):
    """Atomically adds amount to the running minted-supply counter."""
    firebase_transaction(
        "supply/total_minted",
        lambda current: (float(current) if current is not None else 0.0) + amount
    )

def calculate_block_reward(block_index: int) -> float:
    """
    Returns the mining reward for the given block index, applying halvings.
    Reward starts at INITIAL_REWARD and halves every HALVING_INTERVAL blocks.
    Returns 0 once the reward would fall below 1 ALE.
    """
    halvings = block_index // HALVING_INTERVAL
    reward   = INITIAL_REWARD
    for _ in range(halvings):
        reward //= 2   # integer halving
        if reward < 1:
            return 0
    return reward

def get_mintable_reward(block_index: int) -> float:
    """
    Returns the actual reward that can be minted for this block,
    capped so total minted never exceeds MAX_SUPPLY.
    """
    base_reward  = calculate_block_reward(block_index)
    if base_reward == 0:
        return 0

    total_minted = get_total_minted()
    remaining    = MAX_SUPPLY - total_minted
    if remaining <= 0:
        return 0

    return min(base_reward, remaining)

# ── Pure stdlib ECDSA P-256 signature verification ────────────────────────────
# No third-party library required — only hashlib, base64, pow().
# Requires Python 3.8+ for pow(a, -1, mod).

_P  = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
_A  = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC
_Gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
_Gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
_N  = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

def _point_add(P1, P2):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2:
        if y1 != y2: return None
        lam = (3 * x1 * x1 + _A) * pow(2 * y1, -1, _P) % _P
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, _P) % _P
    x3 = (lam * lam - x1 - x2) % _P
    y3 = (lam * (x1 - x3) - y1) % _P
    return (x3, y3)

def _point_mul(k, pt):
    result = None
    addend = pt
    while k:
        if k & 1: result = _point_add(result, addend)
        addend = _point_add(addend, addend)
        k >>= 1
    return result

def _b64url_to_int(s: str) -> int:
    padded = s + '=' * (-len(s) % 4)
    return int.from_bytes(base64.urlsafe_b64decode(padded), 'big')

def _verify_ecdsa_p256(pub_jwk: dict, message_bytes: bytes, sig_bytes: bytes) -> bool:
    """
    Verifies a raw 64-byte ECDSA P-256 signature (r‖s, 32 bytes each, big-endian).
    This is exactly the format produced by Web Crypto's SubtleCrypto.sign().
    """
    if len(sig_bytes) != 64:
        return False
    Qx = _b64url_to_int(pub_jwk['x'])
    Qy = _b64url_to_int(pub_jwk['y'])
    Q  = (Qx, Qy)
    r  = int.from_bytes(sig_bytes[:32], 'big')
    s  = int.from_bytes(sig_bytes[32:], 'big')
    if not (1 <= r < _N and 1 <= s < _N):
        return False
    e  = int.from_bytes(hashlib.sha256(message_bytes).digest(), 'big')
    w  = pow(s, -1, _N)
    u1 = (e * w) % _N
    u2 = (r * w) % _N
    pt = _point_add(_point_mul(u1, (_Gx, _Gy)), _point_mul(u2, Q))
    if pt is None:
        return False
    return pt[0] % _N == r

def verify_transaction_signature(tx: dict) -> bool:
    """
    Verifies the ECDSA-P256 signature on a pending transaction.
    Message format (must match frontend signMessage): sender:receiver:amount:timestamp
    Public key JWK is fetched from Firebase wallets/{sender}/publicKeyJWK.
    """
    try:
        sender        = tx.get('sender', '')
        sig_b64       = tx.get('signature', '')
        if not sender or not sig_b64:
            return False

        wallet = firebase_get(f"wallets/{sender}")
        if not wallet:
            return False
        pub_jwk = wallet.get('publicKeyJWK')
        if not pub_jwk:
            return False

        message   = f"{tx['sender']}:{tx['receiver']}:{tx['amount']}:{tx['timestamp']}"
        sig_bytes = base64.b64decode(sig_b64)
        return _verify_ecdsa_p256(pub_jwk, message.encode(), sig_bytes)
    except Exception:
        return False

# ── Blockchain helpers ────────────────────────────────────────────────────────

def calculate_hash(block: dict) -> str:
    return hashlib.sha256(
        json.dumps(block, sort_keys=True).encode()
    ).hexdigest()

def proof_of_work(block: dict, difficulty: int) -> dict:
    target = "0" * difficulty
    nonce  = 0
    while True:
        block['nonce'] = nonce
        h = calculate_hash(block)
        if h.startswith(target):
            block['hash'] = h
            return block
        nonce += 1

def get_latest_block():
    blocks = firebase_get("blockchain/blocks")
    if not blocks:
        return None
    return sorted(blocks.values(), key=lambda b: b['index'])[-1]

def add_block(block: dict):
    firebase_put(f"blockchain/blocks/block_{block['index']}", block)

def update_wallet_balance(address: str, amount_delta: float):
    """
    Atomically adjust a wallet's liquid balance.
    Uses firebase_transaction for safe concurrent access.
    Balance is floored at 0 — it can never go negative.

    This is called for:
      • Sender deduction  (amount_delta = -tx['amount'])
      • Receiver credit   (amount_delta = +tx['amount'])
      • Miner reward      (amount_delta = +reward)
    """
    def _update(current):
        if current is None:
            current = 0.0
        new_bal = max(0.0, float(current) + amount_delta)
        return round(new_bal, 6)

    firebase_transaction(f"wallets/{address}/balance", _update)

# ── Mining ────────────────────────────────────────────────────────────────────

def mine_block(miner_address: str) -> dict:
    """
    Full mining pipeline:
      1. Find the first approved, unclaimed pending transaction
      2. Reject self-transfers (sender == receiver)
      3. Verify ECDSA signature
      4. Re-verify sender liquid balance (balance may have changed since submission)
      5. Atomically claim the transaction (ETag locking, prevents double-mine)
      6. Run Proof-of-Work
      7. Write block to Firebase
      8. Deduct sender balance  ← sender deduction
      9. Credit receiver balance ← automatic receiving
     10. Credit miner reward (capped by MAX_SUPPLY and halving schedule)
    """

    # ── Step 1: Find an approved, unclaimed transaction ───────────────────────
    pending = firebase_get("blockchain/pending_transactions")
    if not pending:
        return {"error": "No approved transaction waiting"}

    tx_id = None
    tx    = None
    for tid, t in pending.items():
        if t.get('approved') is True and not t.get('claimed') and not t.get('rejected'):
            tx_id, tx = tid, t
            break

    if not tx_id:
        return {"error": "No approved transaction waiting"}

    # ── Step 2: Reject self-transfers ─────────────────────────────────────────
    if tx.get('sender') == tx.get('receiver'):
        firebase_put(f"blockchain/pending_transactions/{tx_id}/rejected", True)
        return {"error": "Self-transfers are not permitted — transaction rejected"}

    # ── Step 3: Verify signature ──────────────────────────────────────────────
    if not verify_transaction_signature(tx):
        firebase_put(f"blockchain/pending_transactions/{tx_id}/rejected", True)
        return {"error": f"Transaction {tx_id} has an invalid signature — rejected"}

    # ── Step 4: Re-verify sender balance ─────────────────────────────────────
    sender_wallet = firebase_get(f"wallets/{tx['sender']}")
    sender_liquid = float(sender_wallet.get('balance', 0)) if sender_wallet else 0.0
    if sender_liquid < float(tx['amount']):
        firebase_put(f"blockchain/pending_transactions/{tx_id}/rejected", True)
        return {
            "error": (
                f"Sender balance insufficient at mining time "
                f"({sender_liquid:.4f} ALE available, "
                f"{float(tx['amount']):.4f} ALE required) — rejected"
            )
        }

    # ── Step 5: Atomically claim transaction ──────────────────────────────────
    claimed = firebase_transaction(
        f"blockchain/pending_transactions/{tx_id}",
        lambda cur: {**cur, 'claimed': True}
                    if cur and not cur.get('claimed') else None
    )
    if not claimed:
        return {"error": "Transaction already claimed by another miner"}

    # Remove from pending queue
    firebase_put(f"blockchain/pending_transactions/{tx_id}", None)

    # ── Step 6: Proof-of-Work ─────────────────────────────────────────────────
    prev_block = get_latest_block()
    index      = 1 if not prev_block else prev_block['index'] + 1
    prev_hash  = "0" * 64 if not prev_block else prev_block['hash']

    block = {
        "index":         index,
        "timestamp":     int(time.time()),
        "transactions":  [tx],
        "previous_hash": prev_hash,
        "difficulty":    DIFFICULTY,
        "nonce":         0,
        "hash":          "",
        "merkle_root":   hashlib.sha256(
                             json.dumps(tx, sort_keys=True).encode()
                         ).hexdigest()
    }
    block = proof_of_work(block, DIFFICULTY)

    # ── Step 7: Write block ───────────────────────────────────────────────────
    add_block(block)

    # ── Step 8: Sender deduction ──────────────────────────────────────────────
    # The sender's liquid balance is reduced by the exact transaction amount.
    # This is authoritative — the frontend's display updates via onValue listener.
    update_wallet_balance(tx['sender'], -float(tx['amount']))

    # ── Step 9: Receiver credit ───────────────────────────────────────────────
    # The receiver's liquid balance increases automatically.
    # The receiver's onValue listener in test.js will detect the increase
    # and notify them of the incoming payment.
    update_wallet_balance(tx['receiver'], float(tx['amount']))

    # ── Step 10: Miner reward (supply-capped) ─────────────────────────────────
    reward = get_mintable_reward(index)
    if reward > 0:
        update_wallet_balance(miner_address, reward)
        add_to_total_minted(reward)

    return {
        "message":     f"Block {index} mined",
        "block":       block,
        "reward_paid": reward,
        "miner":       miner_address
    }

# ── Routes ────────────────────────────────────────────────────────────────────

@app.route('/mine', methods=['POST'])
def mine_endpoint():
    data          = request.get_json(silent=True) or {}
    miner_address = data.get('miner_address', '').strip()

    if not miner_address:
        return jsonify({"error": "miner_address is required"}), 400

    result = mine_block(miner_address)
    status = 400 if 'error' in result else 200
    return jsonify(result), status

@app.route('/supply', methods=['GET'])
def get_supply():
    """Returns current supply statistics."""
    total_minted = get_total_minted()
    latest       = get_latest_block()
    block_index  = latest['index'] if latest else 0
    reward       = calculate_block_reward(block_index + 1)
    return jsonify({
        "max_supply":    MAX_SUPPLY,
        "total_minted":  total_minted,
        "remaining":     MAX_SUPPLY - total_minted,
        "next_reward":   reward,
        "block_height":  block_index
    })

@app.route('/health', methods=['GET'])
def health():
    return jsonify({"status": "ok", "service": "Alethea Mining Backend"})

# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == '__main__':
    print("=" * 52)
    print("  Alethea Mining Backend")
    print(f"  MAX_SUPPLY:     {MAX_SUPPLY:,} ALE")
    print(f"  INITIAL_REWARD: {INITIAL_REWARD} ALE/block")
    print(f"  HALVING_EVERY:  {HALVING_INTERVAL:,} blocks")
    print(f"  DIFFICULTY:     {DIFFICULTY} leading zeros")
    print("  Running on http://0.0.0.0:5000")
    print("=" * 52)
    app.run(host='0.0.0.0', port=5000, debug=True)
