module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem root_ne_zero {v : V} (hv : B v v = 2) : v ≠ 0 := by
  rintro rfl
  rw [map_zero] at hv
  exact absurd hv (by decide)

theorem rootRefl_fix_iff {v : V} (hv : B v v = 2) (d : V) :
    rootRefl (B := B) v hv d = d ↔ B v d = 0 := by
  rw [rootRefl_apply]
  constructor
  · intro h
    rcases smul_eq_zero.mp (sub_eq_self.mp h) with h0 | h0
    · exact h0
    · exact absurd h0 (root_ne_zero hv)
  · intro h
    rw [h, zero_smul, sub_zero]

private theorem two_smul_two_smul (v : V) : (2 : ZMod 3) • (2 : ZMod 3) • v = v := by
  rw [smul_smul, show (2 * 2 : ZMod 3) = 1 by decide, one_smul]

private theorem two_smul_eq_neg (v : V) : (2 : ZMod 3) • v = -v := by
  apply eq_neg_of_add_eq_zero_left
  calc (2 : ZMod 3) • v + v = ((2 : ZMod 3) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show ((2 : ZMod 3) + 1) = 0 by decide, zero_smul]

theorem rootRefl_eq_iff {a b : V} (ha : B a a = 2) (hb : B b b = 2) :
    rootRefl (B := B) a ha = rootRefl (B := B) b hb ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have h1 : rootRefl (B := B) a ha a = rootRefl (B := B) b hb a := by rw [h]
    rw [rootRefl_apply, rootRefl_apply, ha] at h1
    have h2 : (2 : ZMod 3) • a = B b a • b := sub_right_injective h1
    rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (B b a) with h0 | h0 | h0
    · rw [h0, zero_smul] at h2
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (by decide)
      · exact absurd h3 (root_ne_zero ha)
    · right
      rw [h0, one_smul, two_smul_eq_neg] at h2
      rw [← h2, neg_neg]
    · left
      rw [h0] at h2
      exact smul_right_injective V (by decide : (2 : ZMod 3) ≠ 0) h2
  · rintro (rfl | rfl)
    · rfl
    · exact rootRefl_neg b hb

theorem rootRefl_commute (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {a b : V} (ha : B a a = 2) (hb : B b b = 2)
    (h : rootRefl (B := B) a ha * rootRefl (B := B) b hb =
      rootRefl (B := B) b hb * rootRefl (B := B) a ha) :
    B a b = 0 ∨ b = a ∨ b = -a := by
  have hnorm : B (rootRefl (B := B) a ha b) (rootRefl (B := B) a ha b) = 2 :=
    rootRefl_self_apply hP hV hB hα ha hb
  have heq : rootRefl (B := B) (rootRefl (B := B) a ha b) hnorm = rootRefl (B := B) b hb := by
    apply LinearEquiv.ext
    intro u
    rw [rootRefl_apply, ← rootRefl_conj hP hV hB hα ha hb u, h, mul_inv_cancel_right]
  rcases (rootRefl_eq_iff hnorm hb).mp heq with h2 | h2
  · left
    rw [rootRefl_apply] at h2
    rcases smul_eq_zero.mp (sub_eq_self.mp h2) with h3 | h3
    · exact h3
    · exact absurd h3 (root_ne_zero ha)
  · right
    rw [rootRefl_apply] at h2
    have h3 : B a b • a = (2 : ZMod 3) • b := by
      have h4 : B a b • a = b - -b := by rw [← h2, sub_sub_cancel]
      rw [h4, sub_neg_eq_add, two_smul]
    rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (B a b) with h0 | h0 | h0
    · rw [h0, zero_smul] at h3
      rcases smul_eq_zero.mp h3.symm with h5 | h5
      · exact absurd h5 (by decide)
      · exact absurd h5 (root_ne_zero hb)
    · right
      rw [h0, one_smul] at h3
      rw [← two_smul_two_smul b, ← h3, two_smul_eq_neg]
    · left
      rw [h0] at h3
      exact (smul_right_injective V (by decide : (2 : ZMod 3) ≠ 0) h3).symm

theorem root_ne_neg_self {v : V} (hv : B v v = 2) : v ≠ -v := by
  intro h
  have h2 : B v v = B v (-v) := by rw [← h]
  rw [LinearMap.BilinForm.neg_right, hv] at h2
  exact absurd h2 (by decide)

theorem rootRefl_conj_iso {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ a b, B (g a) (g b) = B a b) {v : V} (hv : B v v = 2) :
    g * rootRefl (B := B) v hv * g⁻¹ = rootRefl (B := B) (g v) (by rw [hg, hv]) := by
  apply LinearEquiv.ext
  intro u
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, rootRefl_apply, rootRefl_apply]
  rw [map_sub, map_smul]
  have hga : g (g⁻¹ u) = u := LinearEquiv.apply_symm_apply g u
  have h := hg v (g⁻¹ u)
  rw [hga] at h
  rw [hga, h]

end CFSG.StandardType.E6QTwo

end
