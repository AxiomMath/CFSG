module

public import Init

public section

namespace CFSG.KC.Co2Census

@[expose] def spP : Nat := 2147483647

@[expose] def dotP (r c : List Nat) : Nat := (List.zipWith (· * ·) r c).sum % spP

@[expose] def trP (B : List (List Nat)) : List (List Nat) :=
  (List.range 8).map fun j => B.map fun r => r.getD j 0

@[expose] def mulRP (A B : List (List Nat)) : List (List Nat) :=
  let Bt := trP B
  A.map fun r => Bt.map fun c => dotP r c

@[expose] def mvRP (A : List (List Nat)) (v : List Nat) : List Nat := A.map fun r => dotP r v

@[expose] def idRP : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j => if i = j then 1 else 0

@[expose] def wordRP (L : Nat → List (List Nat)) (w : List Nat) : List (List Nat) :=
  w.foldr (fun k acc => mulRP (L k) acc) idRP

@[expose] def rowsP (A : Array Int) : List (List Nat) :=
  (List.range 8).map fun i => (List.range 8).map fun j => (A[8 * i + j]! % (spP : Int)).toNat

@[expose] def negVP (v : List Nat) : List Nat := v.map fun x => (spP - x % spP) % spP

end CFSG.KC.Co2Census

end
