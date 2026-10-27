module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def K_L2SzAutRank : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) [L.Normal] (m : ℕ),
    IsSimpleGroup ↥L → ¬ IsMulCommutative ↥L →
      Subgroup.centralizer (L : Set A) = ⊥ → IsPGroup 2 (A ⧸ L) →
        (CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 ↥L m ∨
          CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz ↥L m) →
        CFSG.Open.pRank 2 (⊤ : Subgroup A) ≤ m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
