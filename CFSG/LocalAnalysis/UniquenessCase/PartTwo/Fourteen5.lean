module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm145 (D : Data G) : Prop :=
  ∀ L₁ L₂ X : Subgroup G, Hyp141 D L₁ L₂ X → ∀ H : Subgroup G, X ≤ H →
    Fstar H = pCoreOf 2 H → Odd (D.M.relIndex H) →
    (∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G),
      ∃ m ∈ (H ⊓ (L₁ ⊔ L₂)) ⊓ normalizer (X : Set G), ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹) →
    7 ∣ Nat.card ↥(H ⊓ D.M) → H ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
