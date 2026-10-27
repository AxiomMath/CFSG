module

public import CFSG.LieType.Steinberg.PartBRankOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Steinberg

private theorem c2slomqi1_y_eq_x_w_x {G : Type*} [Group G] {F : Type*} [Field F]
    (R : RankOneRels G F) (u : F) :
    R.y u = R.x u⁻¹ * R.w (-u⁻¹) * R.x u⁻¹ := by
  have h1 : R.w (-u⁻¹) = R.x (-u⁻¹) * R.y u * R.x (-u⁻¹) := by
    rw [R.w_def, inv_neg, inv_inv, neg_neg]
  rw [h1]
  have hx : R.x u⁻¹ * R.x (-u⁻¹) = 1 := by
    rw [← R.x_add, add_neg_cancel, R.x_zero]
  have hx' : R.x (-u⁻¹) * R.x u⁻¹ = 1 := by
    rw [← R.x_add, neg_add_cancel, R.x_zero]
  calc R.y u = (R.x u⁻¹ * R.x (-u⁻¹)) * R.y u * (R.x (-u⁻¹) * R.x u⁻¹) := by
        rw [hx, hx', one_mul, mul_one]
    _ = _ := by group

theorem omq_rankOneRels_x_mul_y {G : Type*} [Group G] {F : Type*} [Field F] [Finite F]
    (R : RankOneRels G F) {s t : F} (hd : 1 + s * t ≠ 0) :
    R.x s * R.y t = R.y (t / (1 + s * t)) * R.h (1 + s * t) * R.x (s / (1 + s * t)) := by
  by_cases ht : t = 0
  · subst ht
    simp [R.y_zero, R.h_one]
  obtain ⟨d, hdd⟩ : ∃ d : F, d = 1 + s * t := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hC : ∀ a b : F, a ≠ 0 → b ≠ 0 → R.h (a * b) = R.h a * R.h b :=
    fun a b ha hb => R.h_mul ha hb
  have hdt : d / t ≠ 0 := div_ne_zero hd ht
  have hy1 : R.y t = R.x t⁻¹ * R.w (-t⁻¹) * R.x t⁻¹ := c2slomqi1_y_eq_x_w_x R t
  have hy2 : R.y (t / d) = R.x (d / t) * R.w (-(d / t)) * R.x (d / t) := by
    have := c2slomqi1_y_eq_x_w_x R (t / d)
    rw [inv_div] at this
    exact this
  have k1 : R.x (d / t) * R.h d = R.h d * R.x ((d ^ 2)⁻¹ * (d / t)) := by
    rw [R.h_mul_x hd, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hd), one_mul]
  have k2 : R.w (-(d / t)) * R.h d = R.w (-t⁻¹) := by
    rw [R.w_eq_h_mul (-(d / t)), mul_assoc, R.w_one_mul_h hC hd, ← mul_assoc,
      ← hC _ _ (neg_ne_zero.2 hdt) (inv_ne_zero hd), R.w_eq_h_mul (-t⁻¹)]
    congr 2
    field_simp
  have k3 : (d ^ 2)⁻¹ * (d / t) + s / d = t⁻¹ := by
    field_simp
    rw [hdd]
    ring
  have k4 : s + t⁻¹ = d / t := by
    field_simp
    rw [hdd]
    ring
  calc R.x s * R.y t = R.x s * (R.x t⁻¹ * R.w (-t⁻¹) * R.x t⁻¹) := by rw [hy1]
    _ = R.x (s + t⁻¹) * R.w (-t⁻¹) * R.x t⁻¹ := by rw [R.x_add]; group
    _ = R.x (d / t) * R.w (-t⁻¹) * R.x t⁻¹ := by rw [k4]
    _ = R.x (d / t) *
          (R.w (-(d / t)) * R.h d) * (R.x ((d ^ 2)⁻¹ * (d / t)) * R.x (s / d)) := by
        rw [k2, ← R.x_add, k3]
    _ = R.x (d / t) * R.w (-(d / t)) * (R.x (d / t) * R.h d) * R.x (s / d) := by
        rw [k1]; group
    _ = _ := by rw [hy2]; group

theorem omq_rankOneRels_x_mul_y_singular {G : Type*} [Group G] {F : Type*} [Field F]
    (R : RankOneRels G F) {s t : F} (hd : 1 + s * t = 0) :
    R.x s * R.y t = R.h s * R.w 1 * R.x (-s) := by
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hd
  have ht : t = -s⁻¹ := by
    field_simp
    linear_combination hd
  subst ht
  have h1 : R.y (-s⁻¹) = R.x (-s) * R.w s * R.x (-s) := by
    have := c2slomqi1_y_eq_x_w_x R (-s⁻¹)
    rw [inv_neg, inv_inv, neg_neg] at this
    exact this
  have hx : R.x s * R.x (-s) = 1 := by
    rw [← R.x_add, add_neg_cancel, R.x_zero]
  rw [h1, R.w_eq_h_mul s]
  calc R.x s * (R.x (-s) * (R.h s * R.w 1) * R.x (-s))
      = (R.x s * R.x (-s)) * (R.h s * R.w 1) * R.x (-s) := by group
    _ = _ := by rw [hx, one_mul]

end CFSG.LocalAnalysis.WeakClosure81
