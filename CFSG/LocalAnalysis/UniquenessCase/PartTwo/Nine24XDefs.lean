module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

@[expose] def KFactL2EvenThreeElts : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (X : Subgroup Z) (n : ℕ), X.Normal → ⁅X, X⁆ = X →
    IsL2 (Bar2 X) (2 * n) → CFSG.Open.pRank 3 (⊤ : Subgroup Z) ≤ 1 →
    ∀ z : Z, IsPGroup 3 (Subgroup.zpowers z) → z ∈ X

@[expose] def KFact913L2Even : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Lb Sb Xb : Subgroup Q) (n : ℕ),
    Lb.Normal → F09.Shape92 ↥Lb → CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤ →
    Xb ≤ Lb → ⁅Xb, Xb⁆ = Xb → Sb ≤ normalizer (Xb : Set Q) → 1 < n →
    IsL2 (Bar2 Xb) (2 * n) → Xb = Lb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
