module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin
open scoped MatrixGroups

@[expose] def KGU35 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), S.Normal → IsPSU 3 5 1 ↥S →
    Subgroup.centralizer (S : Set X) = ⊥ →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 4 →
    ∀ (R K : Subgroup X), R ≠ ⊥ → IsPGroup 2 ↥R → K ≤ S → ⁅K, K⁆ = K →
      K ≤ Subgroup.normalizer (R : Set X) →
      Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X) →
      (∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker) →
      (R ⊓ S = ⊥ ∧ Nat.card ↥R = 2) ∨
        ∀ x ∈ K, orderOf x = 5 → ∃ a ∈ S, ∃ b ∈ S, x = a * b * a⁻¹ * b⁻¹ ∧
          ∀ g ∈ Subgroup.closure ({a, b} : Set X), g ^ 5 = 1 ∧ g * x = x * g

end CFSG.Quasithin.H13.Ch4
