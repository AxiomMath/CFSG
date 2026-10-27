module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def K_19_26_rankOne : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K V : Subgroup Y) (e : Y),
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) → CFSG.Open.pRank 3 K ≤ 1 →
    CFSG.Open.IsElemAbelian 2 V → 4 ≤ Nat.card V → V ≤ normalizer (K : Set Y) →
    V ⊓ centralizer (K : Set Y) = ⊥ → CFSG.CGT.Timmesfeld75.IsTI V →
    V ≤ centralizer (((Subgroup.center ↥K).map K.subtype : Subgroup Y) : Set Y) →
    orderOf e = 3 → e ∈ normalizer (K : Set Y) → V ≤ centralizer ({e} : Set Y) →
    (e ∈ K ∨ ¬ 3 ∣ Nat.card K) →
    K ≤ (K ⊓ centralizer ({e} : Set Y)) ⊔ (K ⊓ centralizer (V : Set Y))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
