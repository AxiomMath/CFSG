module

public import Certificates.Data.CFSGNative.PairSchreier.Preds

public section

namespace CFSG.Sporadic.Schreier.PairNative

@[expose] def countOrd (bs : List Nat) (m : Nat) (Bs : List (Array (Array Nat))) : Nat :=
  countW (ordPred bs m) Bs []

@[expose] def countPair (bs : List Nat) (my : Nat) (x : List (Array Nat))
    (conds : List (List Bool × Nat)) (Bs : List (Array (Array Nat))) : Nat :=
  countW (pairPred bs my x conds) Bs []

@[expose] def leafPair2 (bs : List Nat) (my : Nat) (x₁ x₂ : List (Array Nat))
    (conds : List (List Bool × Nat)) (y : List (Array Nat)) : Nat × Nat × Nat :=
  if ordB bs y my then
    (1, if condsOK bs x₁ y conds then 1 else 0, if condsOK bs x₂ y conds then 1 else 0)
  else (0, 0, 0)

@[inline, expose] def add3 (a b : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

@[expose] def countPair2W (bs : List Nat) (my : Nat) (x₁ x₂ : List (Array Nat))
    (conds : List (List Bool × Nat)) :
    List (Array (Array Nat)) → List (Array Nat) → Nat × Nat × Nat
  | [], acc => leafPair2 bs my x₁ x₂ conds acc
  | B :: Bs, acc =>
    B.foldl (fun c t => add3 c (countPair2W bs my x₁ x₂ conds Bs (t :: acc))) (0, 0, 0)

end CFSG.Sporadic.Schreier.PairNative
