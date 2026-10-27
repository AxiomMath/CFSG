module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint (LieModel)

@[expose] def LiftsConjugate {S : Type} [Group S] (x : S) : Prop :=
  ∀ (L : Type) [Group L] (π : L →* S), Function.Surjective π → π.ker ≤ Subgroup.center L →
    Group.IsPerfect L → Nat.card π.ker = 3 →
      ∀ x' : L, π x' = x → ∀ z ∈ π.ker, ∃ c : L, c * x' * c⁻¹ = x' * z

@[expose] def OmegaSevenInvolData : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .POmegaOdd 3 3 1 →
    ∀ σ : MulAut S, orderOf σ = 2 →
      (∃ x : S, orderOf x = 3 ∧ σ x = x⁻¹ ∧ LiftsConjugate x) ∨
      (∃ (g : S) (τ : MulAut S), τ = MulAut.conj g * σ * (MulAut.conj g)⁻¹ ∧ τ * σ = σ * τ ∧
        τ ≠ σ ∧ ∃ x : S, orderOf x = 3 ∧ (σ * τ) x = x⁻¹ ∧ LiftsConjugate x)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
