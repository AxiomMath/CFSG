module

public import Certificates.Data.HNUnitaryBridge

public section

namespace CFSG.KC.HN14969

open HNUnitaryBridge

@[expose] def lget (l : List Nat) (x : Nat) : Nat := l.getD x 0

@[expose] def compL (p q : List Nat) : List Nat := q.map (lget p)

@[expose] def smallL (k : Nat) : List Nat := smallPermLists.toList.getD k []

@[expose] def evalWordL (ws : List Nat) : List Nat :=
  ws.foldr (fun k acc => compL (smallL k) acc) (List.range 50)

@[expose] def sigmaAL : List Nat := smallL 0

@[expose] def sigmaBL : List Nat := evalWordL wordB

@[expose] def evalABL (L : List Bool) : List Nat :=
  L.foldr (fun b acc => compL (if b then sigmaBL else sigmaAL) acc) (List.range 50)

@[expose] def wordsOKL : Bool :=
  (List.range 6).all fun k => evalABL (wordsAB.getD k []) == smallL k

@[expose] def fconj (x : Nat) : Nat := x % 5 + 5 * ((5 - x / 5 % 5) % 5)

@[expose] def mvL (M v : List Nat) : List Nat :=
  [0, 1, 2].map fun r => fadd (fadd (fmul (lget M (3 * r)) (lget v 0))
    (fmul (lget M (3 * r + 1)) (lget v 1))) (fmul (lget M (3 * r + 2)) (lget v 2))

@[expose] def firstNZL (v : List Nat) : Nat :=
  if lget v 0 ≠ 0 then lget v 0 else if lget v 1 ≠ 0 then lget v 1 else lget v 2

@[expose] def normL (v : List Nat) : List Nat := v.map (fmul (finv (firstNZL v)))

@[expose] def hermL (v : List Nat) : Nat :=
  fadd (fadd (fmul (lget v 0) (fconj (lget v 0))) (fmul (lget v 1) (fconj (lget v 1))))
    (fmul (lget v 2) (fconj (lget v 2)))

@[expose] def isoPtOK (v : List Nat) : Bool :=
  v.length == 3 && v.all (fun x => decide (x < 25)) && firstNZL v == 1 && hermL v == 0

@[expose] def distinctL : List (List Nat) → Bool
  | [] => true
  | v :: vs => !vs.contains v && distinctL vs

@[expose] def ptsOK (X : List (List Nat)) : Bool :=
  X.length == 126 && X.all isoPtOK && distinctL X

@[expose] def actOK (M : List Nat) (X : List (List Nat)) (g : Nat → Nat) : Bool :=
  (List.range 126).all fun i =>
    decide (g i < 126) && normL (mvL M (X.getD i [])) == X.getD (g i) []

@[expose] def agreeL (n : Nat) (g h : Nat → Nat) : Bool := (List.range n).all fun i => g i == h i

@[expose] def isListL (g : Nat → Nat) (l : List Nat) : Bool := (List.range l.length).map g == l

@[expose] def letter (c : Nat) : Int :=
  if c % 2 = 0 then Int.ofNat (c / 2 + 1) else -Int.ofNat (c / 2 + 1)

@[expose] def decW (D : List (List Nat)) : List (List Int) := D.map (List.map letter)

end CFSG.KC.HN14969

end
