module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

@[expose] def L3NotEvenClassical : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ ℓ f : ℕ,
    ((ℓ ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 3 ℓ f) ∨
      (ℓ ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 ℓ f)) →
    ¬ CFSG.AGLEmbedding.IsOrthogonalTwo X ∧
      (ℓ ≠ 2 → ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (X ⧸ Subgroup.center X))

@[expose] def L3EvenParabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ f : ℕ, 2 ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel X .PSL 3 2 f) ∨
      (∃ f : ℕ, 2 ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel X .PSU 3 2 f)) →
    ∀ J K : Subgroup X, J ≠ ⊤ → CFSG.AGLEmbedding.IsParabolicTwo ⊤ J → K ≤ J →
      ⁅K, K⁆ = K → K ≠ ⊥ →
      ∃ g ∈ J, ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf g = r ∧ r ∣ Nat.card K ∧
        ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 J

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
