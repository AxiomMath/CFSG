module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

@[expose] def L3Overgroup : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ ℓ f : ℕ, ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel X .PSL 3 ℓ f) ∨
      (∃ ℓ f : ℕ, ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel X .PSU 3 ℓ f)) →
    ∀ Z Y K : Subgroup X, Nat.card Z = 3 → Subgroup.normalizer (Z : Set X) ≤ Y →
      Y ≤ Subgroup.normalizer (K : Set X) → ⁅K, K⁆ = K → Z ≤ K →
      ⁅CFSG.Open.pCoreOf 2 K, Z⁆ ≠ ⊥ →
      ∃ g ∈ Y, ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf g = r ∧ r ∣ Nat.card K ∧
        ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
