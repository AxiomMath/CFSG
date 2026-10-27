module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.F4

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

@[expose] def LayerClaimsF4 (p : ℕ) {G : Type} [Group G] (α : MulAut G) (Q : Subgroup G) : Prop :=
  (∀ e ∈ Q, ¬ ∀ g ∈ Q, α g = e * g * e⁻¹) ∧
  (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
    LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
  ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
    (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

end CFSG.RankThree.PartOne.TCX.F4
