module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

@[expose] def E8LeviRankLE3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    orderOf ((Nat.card K : ℕ) : ZMod p) ∈ ({3, 4, 6} : Set ℕ) →
    ∀ J : Set (Fin Tag.E8.rank), J ≠ Set.univ →
      ∀ E : Subgroup (ModGL Tag.E8 K), E ≤ subsystemGroup Tag.E8 K J →
        IsElemAbelian p E → Nat.card E ≤ p ^ 3

end CFSG.StandardType
