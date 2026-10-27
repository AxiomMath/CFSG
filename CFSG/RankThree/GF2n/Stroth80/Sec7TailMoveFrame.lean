module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

structure MoveFrame {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [Group X] (B : LinearMap.BilinForm K E) (φ : X →* (E ≃ₗ[K] E))
    (V L Nb Rb : Subgroup X) (Tt : X → Submodule K E) (q : ℕ) : Prop where
  char2 : (2 : K) = 0
  nondeg : B.Nondegenerate
  refl : B.IsRefl
  inj : Function.Injective φ
  isom : ∀ x u v, B (φ x u) (φ x v) = B u v
  V_le_L : V ≤ L
  L_le_Nb : L ≤ Nb
  Nb_le_Rb : Nb ≤ Rb
  V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  V_sq : ∀ a ∈ V, a * a = 1
  V_card : Nat.card V = q
  q_ge : 4 ≤ q
  ti : ∀ g : X, ∀ a ∈ V, a ≠ 1 → g * a * g⁻¹ ∈ V → g ∈ normalizer (V : Set X)
  L_comm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a
  L_card : Nat.card L = q ^ 5
  L_norm : ∀ k ∈ normalizer (V : Set X), ∀ l ∈ L, k * l * k⁻¹ ∈ L
  Rb_le_K : ∀ r ∈ Rb, r ∈ normalizer (V : Set X)
  Nb_comm : ∀ a ∈ Nb, ∀ b ∈ Nb, ⁅a, b⁆ ∈ V
  Nb_center : ∀ z ∈ Nb, (∀ n ∈ Nb, z * n = n * z) → z ∈ V
  Nb_semi : ∀ z ∈ Nb, z ∉ V → ∀ w ∈ V, ∃ m ∈ Nb, m * z * m⁻¹ = w * z
  Nb_bound : ∀ A : Subgroup X, A ≤ Nb → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 5
  Nb_pgroup : IsPGroup 2 Nb
  semilinear : ∀ Y : Subgroup X, Y ≤ normalizer (V : Set X) → (∀ y ∈ Y, y * y = 1) →
    (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) →
      Nat.card Y ≤ 2 * Nat.card ↥(centralizer (V : Set X) ⊓ Y)
  two_elements : ∀ k ∈ normalizer (V : Set X), (∀ a ∈ V, k * a = a * k) →
    IsPGroup 2 (zpowers k) → k ∈ Rb
  CL : ∀ r ∈ Rb, (∀ l ∈ L, r * l = l * r) → r ∈ L
  Tt_range : ∀ (g : X), ∀ a ∈ V, a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g
  Tt_rank : ∀ g : X, Module.finrank K (Tt g) = 6
  Nb_fixes : ∀ n ∈ Nb, ∀ w ∈ Tt 1, φ n w = w
  Rb_fix_Nb : ∀ r ∈ Rb, (∀ w ∈ Tt 1, φ r w = w) → r ∈ Nb
  quad : ∀ s ∈ L, ∀ u ∈ L, ∀ w, opm (φ s) (opm (φ u) w) = 0
  pair_dim : ∀ g₁ g₂ : X,
    (∀ a ∈ V, ∀ b ∈ V, (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) = (g₂ * b * g₂⁻¹) * (g₁ * a * g₁⁻¹)) →
    (∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Rb) →
    (¬ ∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Nb) →
      Module.finrank K ↥(Tt g₁ ⊓ Tt g₂) = 2
  image_dim : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    2 ≤ Module.finrank K ↥((Tt g).map (B.orthogonal (Tt 1)).mkQ)
  no_isotropic : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    ∀ Lm : Submodule K E, Tt 1 ≤ Lm → Lm ≤ B.orthogonal (Tt 1) →
      (∀ r ∈ Rb, ∀ w ∈ Lm, φ r w ∈ Lm) → (∀ x ∈ Lm, ∀ y ∈ Lm, B x y = 0) →
      ∀ a ∈ V, a ≠ 1 →
        ¬ ((B.orthogonal (Tt 1)).map (opm (φ (g * a * g⁻¹))) ≤ Lm)
  transvection : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
    ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ L, ⁅g * a * g⁻¹, ⁅x, g * b * g⁻¹⁆⁆ ∈ V

end CFSG.RankThree.GF2n.Stroth80
