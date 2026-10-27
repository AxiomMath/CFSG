module

public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def G64CommTransvFact : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (a : MulAut V), G64.Hyp61 G a →
      Nat.card ↥(commV (Subgroup.zpowers a)) = 2 → G64.Conclusion G a →
    ∀ P : Subgroup (MulAut V), IsSylowTwoOf P G →
    ∀ v₁ : V, commV (Subgroup.zpowers a) = Subgroup.zpowers v₁ →
    ∀ g ∈ G, a * (g⁻¹ * a * g) = g⁻¹ * a * g * a → g⁻¹ v₁ ≠ v₁ →
      (∃ X : Subgroup (MulAut V), P ≤ X ∧ X < G ∧ ∃ x ∈ X, orderOf x = 3) ∨
      ∃ y ∈ G, y (g⁻¹ v₁) = g⁻¹ v₁ ∧ orderOf y = 3 ∧ y v₁ ≠ v₁ ∧
        ∀ z ∈ G, z (g⁻¹ v₁) = g⁻¹ v₁ → Odd (orderOf z) → z ∈ Subgroup.zpowers y

end CFSG.Quasithin.Vol2.Ch10.SecG
