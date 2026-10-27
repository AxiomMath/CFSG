module

public import Certificates.Data.HNUnitaryBridge

public section

namespace CFSG.Quasithin.H13.KGU35

open HNUnitaryBridge

@[expose] def cNeg (x : Nat) : Nat := (5 - x % 5) % 5 + 5 * ((5 - x / 5 % 5) % 5)

@[expose] def cConj (x : Nat) : Nat := x % 5 + 5 * ((5 - x / 5 % 5) % 5)

@[expose] def ent (A : Array Nat) (k : Nat) : Nat := A.getD k 0

@[expose] def mMul (A B : Array Nat) : Array Nat :=
  (List.range 9).toArray.map (mprod (ent A) (ent B))

@[expose] def mId : Array Nat := #[1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def mPow (A : Array Nat) : Nat → Array Nat
  | 0 => mId
  | k + 1 => mMul A (mPow A k)

end CFSG.Quasithin.H13.KGU35
