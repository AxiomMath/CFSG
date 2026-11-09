module

public import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.KC.WordRelK

open CFSG.Monster.B

@[expose] def packP (y : Model.Pauli) : Nat :=
  y.2.1 + 4096 * y.2.2 + (bif y.1 then 16777216 else 0)

@[expose] def unpackP (x : Nat) : Model.Pauli :=
  (Nat.beq (x / 16777216 % 2) 1, x % 4096, x / 4096 % 4096)

@[expose] def foldX (k v : Nat) : Nat := v ^^^ (v >>> k)

@[expose] def par12 (v : Nat) : Nat := foldX 1 (foldX 2 (foldX 4 (foldX 8 v))) % 2

@[expose] def mulP (x y : Nat) : Nat :=
  x ^^^ y ^^^ par12 ((y % 4096) &&& (x / 4096 % 4096)) * 16777216

@[expose] def basisP (k : Nat) : Model.Pauli :=
  bif Nat.blt k 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12))

@[expose] def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && f k) n

@[expose] def rowAt (T r : Nat) : Nat := (T >>> (600 * r)) % 2 ^ 600

@[expose] def entryAt (row k : Nat) : Nat := (row >>> (25 * k)) % 33554432

@[expose] def applyRow (row y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc yb rb =>
      ih (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
        (rb / 33554432))
    24 (y / 16777216 * 16777216) (y % 16777216) row

end CFSG.KC.WordRelK
