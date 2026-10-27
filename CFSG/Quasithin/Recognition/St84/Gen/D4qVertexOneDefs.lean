module

public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.F112R.St84

open scoped MatrixGroups

variable {G : Type*} [Group G]

structure D4qVertexOneData (Q Z K H : Subgroup G) (f : ℕ) : Prop where
  special : IsSpecialPow 2 (2 ^ f) 4 ↥Q
  centerOf_eq : centerOf Q = Z
  levi_le_normalizer : K ≤ Subgroup.normalizer (Q : Set G)
  torus_le_normalizer : H ≤ Subgroup.normalizer (Q : Set G)
  disjoint : Disjoint Q (K ⊔ H)
  levi_inf_torus : K ⊓ H = ⊥
  levi_commute_torus : ∀ k ∈ K, ∀ h ∈ H, k * h = h * k
  levi_mulEquiv : Nonempty (↥K ≃* SL(2, GaloisField 2 (3 * f)))
  levi_centralizes : ∀ k ∈ K, ∀ z ∈ Z, k * z * k⁻¹ = z
  irreducible : ∀ W : Subgroup G, Z ≤ W → W ≤ Q → K ≤ Subgroup.normalizer (W : Set G) →
    W = Z ∨ W = Q
  card_torus : Nat.card H = 2 ^ f - 1
  torus_comm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  torus_faithful : ∀ h ∈ H, (∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ Z) → h = 1

end CFSG.Quasithin.F112R.St84

end
