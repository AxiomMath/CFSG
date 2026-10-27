module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Om4Facts {V : Type*} [CommGroup V] (X : Subgroup (MulAut V)) : Prop where
  card_eq : Nat.card X = 36
  card_oTwoUpper : Nat.card (oTwoUpper X) = 9
  stab : ∀ B A : Subgroup (MulAut V), B ≤ X → Nat.card B = 2 →
    (∀ b ∈ B, b ≠ 1 → ∀ e ∈ oTwoUpper X, b * e = e * b → e = 1) → A ≤ oTwoUpper X → A ≠ ⊥ →
    (¬ ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
    ∃ z : V, z ≠ 1 ∧ z ∈ commV B ∧ (∀ g ∈ X, g z = z ↔ g ∈ A ⊔ B) ∧
      ∃ t ∈ X, (∀ b ∈ B, t * b = b * t) ∧ t z ≠ z

@[expose] def Om4FactsStatement : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)), IsOmegaFourPlus X → Om4Facts X

end CFSG.Quasithin
