module

public import Certificates.Data.Kernel.S1277KGm

public section

namespace CFSG.KC.S1277Mod

open CFSG.KC.S1277Gm

@[expose] def allLt (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => f i && ih) n

@[expose] def rd6 (P n : ℕ) : ℕ := (P >>> (6 * n)) % 64

@[expose] def mulP (nb AP CP x y : ℕ) : ℕ :=
  rd6 CP (x / 64 * nb + y / 64) * 64 + (x % 64 ^^^ rd6 AP (x / 64 * 64 + y % 64))

@[expose] def invP (AP IP x : ℕ) : ℕ :=
  rd6 IP (x / 64) * 64 + rd6 AP (rd6 IP (x / 64) * 64 + x % 64)

@[expose] def pwP (nb CP idb i : ℕ) : ℕ → ℕ
  | 0 => idb
  | n + 1 => rd6 CP (i * nb + pwP nb CP idb i n)

@[expose] def apChk (L : List ℕ) (AP : ℕ) : Bool :=
  Nat.beq (AP >>> (6 * (L.length * 64))) 0 &&
    allLt L.length fun i => allLt 64 fun c => Nat.beq (rd6 AP (i * 64 + c)) (appP (L.getD i 0) c)

@[expose] def agree (AP i k : ℕ) : Bool :=
  allLt 6 fun f => Nat.beq (rd6 AP (i * 64 + 2 ^ f)) (rd6 AP (k * 64 + 2 ^ f))

@[expose] def cpChk (nb AP CP : ℕ) : Bool :=
  Nat.beq (CP >>> (6 * (nb * nb))) 0 &&
    allLt nb fun i => allLt nb fun j =>
      Nat.blt (rd6 CP (i * nb + j)) nb &&
        allLt 6 fun f => Nat.beq (rd6 AP (rd6 CP (i * nb + j) * 64 + 2 ^ f))
          (rd6 AP (i * 64 + rd6 AP (j * 64 + 2 ^ f)))

@[expose] def ndChk (nb AP : ℕ) : Bool :=
  allLt nb fun i => allLt nb fun k => Nat.beq i k || !agree AP i k

@[expose] def ipChk (nb AP CP IP idb : ℕ) : Bool :=
  Nat.blt idb nb && (allLt 6 fun f => Nat.beq (rd6 AP (idb * 64 + 2 ^ f)) (2 ^ f)) &&
    Nat.beq (IP >>> (6 * nb)) 0 &&
    allLt nb fun i => Nat.beq (rd6 IP i) (pwP nb CP idb i 59)

@[expose] def invChk (nb AP CP IP idb : ℕ) : Bool :=
  allLt (nb * 64) fun n =>
    Nat.blt (invP AP IP n) (nb * 64) && Nat.beq (mulP nb AP CP n (invP AP IP n)) (idb * 64)

@[expose] def modChk (L : List ℕ) (AP CP IP idb : ℕ) : Bool :=
  apChk L AP && cpChk L.length AP CP && ndChk L.length AP && ipChk L.length AP CP IP idb &&
    invChk L.length AP CP IP idb

end CFSG.KC.S1277Mod

end
