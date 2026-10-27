module

public section

namespace Certificates.Data.LieSylRootWt

inductive Ty where
  | G2
  | D4
  | F4
  deriving DecidableEq, Repr

@[expose] def Ty.rank : Ty → Nat
  | .G2 => 2
  | .D4 => 4
  | .F4 => 4

@[expose] def Ty.codes : Ty → List Nat
  | .G2 =>
    [137, 152, 135, 185, 153, 120, 87, 186, 169, 119, 86, 103]
  | .D4 =>
    [34953, 34968, 35208, 39048, 34951, 35209, 34936, 35224, 34696, 39304, 30856, 34695, 35225,
     39305, 34680, 39320, 30600, 34679, 30599, 39321, 30584, 30583, 39577, 30327]
  | .F4 =>
    [34953, 34968, 35208, 39048, 34951, 34969, 34936, 35480, 35224, 34696, 39304, 30856, 34935,
     35481, 34424, 43672, 35225, 39320, 34680, 30600, 34423, 35497, 43673, 26232, 39321, 39576,
     34679, 30584, 34407, 26231, 43689, 39577, 30583, 30328, 26215, 44201, 39593, 30327, 25703,
     44217, 39849, 30311, 25687, 44218, 43945, 30055, 25686, 25959]

@[expose] def decodeVec (r code : Nat) : List Int :=
  List.ofFn fun j : Fin r => ((code / 16 ^ (j : Nat) % 16 : Nat) : Int) - 8

@[expose] def Ty.roots (t : Ty) : List (List Int) :=
  t.codes.map (decodeVec t.rank)

@[expose] def red (ℓ : Nat) (x : Int) : Int := x % (ℓ : Int)

@[expose] def redV (ℓ : Nat) (v : List Int) : List Int := v.map (red ℓ)

@[expose] def comboAt (r : Nat) (b : List Int) (γs : List (List Int)) (i : Nat) : Int :=
  ((List.range r).map fun j => b.getD j 0 * (γs.getD j []).getD i 0).sum

@[expose] def combo (r : Nat) (b : List Int) (γs : List (List Int)) : List Int :=
  (List.range r).map (comboAt r b γs)

@[expose] def unitVec (r j : Nat) : List Int :=
  (List.range r).map fun i => if i = j then 1 else 0

@[expose] def level (r : Nat) (b : List Int) : Nat :=
  (List.range r).foldl (fun acc i => if b.getD i 0 ≠ 0 then i else acc) 0

@[expose] def iterN {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterN f n (f x)

@[expose] def orderOK (ℓ e r : Nat) (γs : List (List Int)) : Bool :=
  (List.range r).all fun j =>
    iterN (fun v => redV ℓ (combo r v γs)) e (unitVec r j) == redV ℓ (unitVec r j)

@[expose] def searchOK (ℓ e r : Nat) (R Rm : List (List Int)) (levels : List (List (List Int))) :
    Nat → Nat → List (List Int) → Bool
  | 0, _, p => orderOK ℓ e r p
  | fuel + 1, k, p =>
    if k < r then
      R.all fun γ =>
        !((levels.getD k []).all (fun b => Rm.contains (redV ℓ (combo r b (p ++ [γ]))))) ||
          searchOK ℓ e r R Rm levels fuel (k + 1) (p ++ [γ])
    else orderOK ℓ e r p

@[expose] def stabCheck (ℓ e r : Nat) (R : List (List Int)) : Bool :=
  searchOK ℓ e r R (R.map (redV ℓ))
    ((List.range r).map fun k => R.filter fun b => level r b == k) r 0 []

@[expose] def rootWeightStabCheck (t : Ty) (ℓ e : Nat) : Bool :=
  stabCheck ℓ e t.rank t.roots

end Certificates.Data.LieSylRootWt
