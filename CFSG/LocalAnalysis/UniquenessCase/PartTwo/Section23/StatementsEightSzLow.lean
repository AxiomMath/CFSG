module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_8_SzLow (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ K ∈ calC D.M, ∀ a : ℕ, IsSz (Bar2 K) a →
    conjClosure D.M K ≠ K → a = 2 ^ CFSG.Open.pRank 2 D.Z - 1 → a.Prime →
    ∀ r : ℕ, r.Prime → r ∣ 2 ^ a - 1 → ∀ A : Subgroup G, Nat.card A = r → A ≤ D.M →
      A ≤ Subgroup.normalizer (D.T : Set G) → A ≤ Subgroup.normalizer (K : Set G) →
        ∃ L₁ ∈ calLLow D.T D.M, A ≤ Subgroup.normalizer (L₁ : Set G) ∧
          ∀ x ∈ A, ∀ b ∈ L₁, b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L₁

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
