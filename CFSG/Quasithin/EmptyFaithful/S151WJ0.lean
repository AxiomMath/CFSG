module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Rank2Data {X : Type} [Group X] (D : Subgroup X) : Prop :=
  Subgroup.normalizer (D : Set X) ≤ D ∧
    ∃ Q₁ Q₂ : Subgroup X, Q₁ ≠ Q₂ ∧ IsMaxSubgroupIn ⊤ Q₁ ∧ IsMaxSubgroupIn ⊤ Q₂ ∧ D ≤ Q₁ ∧ D ≤ Q₂ ∧
      Nat.card ↥Q₁ = 3 * Nat.card ↥D ∧ Nat.card ↥Q₂ = 3 * Nat.card ↥D ∧ CharTwo Q₁ ∧ CharTwo Q₂ ∧
      ∀ K : Subgroup X, IsMaxSubgroupIn ⊤ K → D ≤ K → K = Q₁ ∨ K = Q₂

end CFSG.Quasithin
