module

public import CFSG.Walter.Ree.ThompsonN
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]

@[expose] def ι₁ (x : k) : k := (1 - x) / (1 + x)

@[expose] def ι₂ (x : k) : k := (x + 1) / (x - 1)

theorem pow_three_eq_self_iff {x : k} : x ^ 3 = x ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  have e : x ^ 3 - x = x * ((x - 1) * (x + 1)) := by ring
  rw [← sub_eq_zero, e, mul_eq_zero, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

theorem sigmaTwo_of_ree {σ : k ≃+* k} (hσ : ∀ x : k, σ (σ x) = x ^ 3) (x : k)
    (h : σ x * x ^ 2 = 1) : x = 1 := by
  have h' : x ^ 3 * σ x ^ 2 = 1 := by
    have := congrArg σ h
    rwa [map_mul, map_pow, hσ, map_one] at this
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have e : x ^ 3 * (x - 1) = 0 := by
    linear_combination x ^ 3 * (σ x * x ^ 2 + 1) * h - x ^ 4 * h'
  rcases mul_eq_zero.1 e with e | e
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 e) hx
  · linear_combination e

theorem sigmaTwo_of_units {σ : k ≃+* k} (h : ∀ t : kˣ, σ t * (t : k) ^ 2 = 1 → t = 1) (x : k)
    (hx : σ x * x ^ 2 = 1) : x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  simpa using congrArg Units.val (h (Units.mk0 x hx0) (by simpa using hx))

section Exponent

variable {σ : k ≃+* k} {a : ℕ}

theorem a_ne_zero (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) : a ≠ 0 := by
  rintro rfl
  simpa using haσ 0

theorem sq_eq_one_of_pow_eq_one (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) {t : k}
    (ht : t ^ a = 1) : t ^ 2 = 1 := by
  rw [← haσ t, mul_pow, ← map_pow, ht, map_one, one_mul]

theorem sq_eq_one_of_pow_two_add_eq_one (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) {t : k} (ht : t ^ (2 + a) = 1) : t ^ 2 = 1 := by
  have e1 := haσ t
  rw [mul_pow] at e1
  have e2 : σ t ^ 2 * σ t ^ a = 1 := by rw [← pow_add, ← map_pow, ht, map_one]
  rw [pow_add] at ht
  have h1 : (σ t * t ^ 2) ^ 2 = 1 := by
    linear_combination (-(σ t ^ 2 * t ^ 2)) * e1 + t ^ 2 * t ^ a * e2 + ht
  rcases sq_eq_one_iff.1 h1 with h | h
  · rw [hσ2 t h, one_pow]
  · have := hσ2 (-t) (by rw [map_neg, neg_sq]; linear_combination -h)
    rw [show t = -1 by linear_combination -this]
    ring

end Exponent

variable [CharP k 3]

theorem three_eq_zero : (3 : k) = 0 := ThompsonN.three_eq_zero

theorem char3_two_ne_zero : (2 : k) ≠ 0 := fun h =>
  one_ne_zero (by linear_combination (three_eq_zero (k := k)) - h)

theorem neg_one_sub_one : (-1 - 1 : k) = 1 := by linear_combination -three_eq_zero (k := k)

theorem ι₂_add_one {x : k} (hx1 : x - 1 ≠ 0) : ι₂ x + 1 = -x / (x - 1) := by
  rw [ι₂, eq_div_iff hx1, add_mul, div_mul_cancel₀ _ hx1]
  linear_combination x * three_eq_zero (k := k)

theorem one_sub_ι₂ {x : k} (hx1 : x - 1 ≠ 0) : 1 - ι₂ x = 1 / (x - 1) := by
  rw [ι₂, eq_div_iff hx1, sub_mul, div_mul_cancel₀ _ hx1]
  linear_combination -three_eq_zero (k := k)

theorem ι₁_add_one {x : k} (hx2 : x + 1 ≠ 0) : ι₁ x + 1 = -1 / (1 + x) := by
  have hx2' : 1 + x ≠ 0 := by rwa [add_comm]
  rw [ι₁, eq_div_iff hx2', add_mul, div_mul_cancel₀ _ hx2']
  linear_combination three_eq_zero (k := k)

theorem ι₁_sub_one {x : k} (hx2 : x + 1 ≠ 0) : ι₁ x - 1 = x / (1 + x) := by
  have hx2' : 1 + x ≠ 0 := by rwa [add_comm]
  rw [ι₁, eq_div_iff hx2', sub_mul, div_mul_cancel₀ _ hx2']
  linear_combination -x * three_eq_zero (k := k)

theorem ι₁_ι₂ {x : k} (hx : x ≠ 0) (hx1 : x - 1 ≠ 0) : ι₁ (ι₂ x) = -x⁻¹ := by
  rw [ι₁, one_sub_ι₂ hx1, add_comm, ι₂_add_one hx1]
  field_simp

theorem ι₂_ι₁ {x : k} (hx : x ≠ 0) (hx2 : x + 1 ≠ 0) : ι₂ (ι₁ x) = -x⁻¹ := by
  have hx2' : 1 + x ≠ 0 := by rwa [add_comm]
  rw [ι₂, ι₁_add_one hx2, ι₁_sub_one hx2]
  field_simp

theorem ι₂_add_one_ne {x : k} (hx : x ≠ 0) (hx1 : x - 1 ≠ 0) : ι₂ x + 1 ≠ 0 := by
  rw [ι₂_add_one hx1]
  exact div_ne_zero (neg_ne_zero.2 hx) hx1

theorem ι₁_sub_one_ne {x : k} (hx : x ≠ 0) (hx2 : x + 1 ≠ 0) : ι₁ x - 1 ≠ 0 := by
  have hx2' : 1 + x ≠ 0 := by rwa [add_comm]
  rw [ι₁_sub_one hx2]
  exact div_ne_zero hx hx2'

theorem klein {f m n c : k → k} {ε : k}
    (h1 : ∀ x, x + 1 ≠ 0 → f x = m x * f (ι₁ x) + n x)
    (h2 : ∀ x, x - 1 ≠ 0 → f x = ε * f (ι₂ x) + c (ι₂ x)) {x : k} (hx : x ≠ 0)
    (hx1 : x - 1 ≠ 0) (hx2 : x + 1 ≠ 0) :
    f x * (m x - m (ι₂ x)) =
      m x * (ε * n (ι₂ x) + c (ι₂ x)) - m x * m (ι₂ x) * c (-x⁻¹) - n x * m (ι₂ x) := by
  have e1 := h1 x hx2
  have e2 := h2 x hx1
  have e3 := h1 (ι₂ x) (ι₂_add_one_ne hx hx1)
  have e4 := h2 (ι₁ x) (ι₁_sub_one_ne hx hx2)
  rw [ι₁_ι₂ hx hx1] at e3
  rw [ι₂_ι₁ hx hx2] at e4
  linear_combination m x * e2 + m x * ε * e3 - m (ι₂ x) * e1 - m (ι₂ x) * m x * e4

theorem quad_ne_zero (hneg : ∀ w : k, w ^ 2 ≠ -1) (x : k) :
    -((x ^ 2 - x - 1) * (x ^ 2 + x - 1)) ≠ 0 := by
  rw [neg_ne_zero]
  refine mul_ne_zero (fun h1 => ?_) (fun h1 => ?_)
  · exact hneg (x + 1) (by linear_combination h1 + (x + 1) * three_eq_zero (k := k))
  · exact hneg (x - 1) (by linear_combination h1 + (1 - x) * three_eq_zero (k := k))

theorem den_ne_zero (hneg : ∀ w : k, w ^ 2 ≠ -1) {e : ℕ} (he : Even e) (he0 : e ≠ 0)
    (h : ∀ t : k, t ^ e = 1 → t ^ 2 = 1) (x : k) : x ^ e - (x ^ 2 - 1) ^ e ≠ 0 := by
  intro hx
  by_cases hx0 : x = 0
  · subst hx0
    norm_num [zero_pow he0, he.neg_one_pow] at hx
  · have ht := h ((x ^ 2 - 1) / x) (by
      rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hx0)]
      exact (sub_eq_zero.1 hx).symm)
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hx0)] at ht
    exact quad_ne_zero hneg x (by linear_combination -ht)

variable {σ : k ≃+* k} {a : ℕ}

theorem sq_ne_neg_one (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (w : k) :
    w ^ 2 ≠ -1 := by
  intro hw
  have h1 : (σ w * w) ^ 2 = 1 := by
    rw [mul_pow, ← map_pow, hw, map_neg, map_one]; ring
  obtain ⟨b, rfl⟩ := ha
  have h2 := haσ w
  rw [hw, ← two_mul, pow_mul, h1, one_pow] at h2
  exact char3_two_ne_zero (by linear_combination h2)

theorem D1_ne_zero (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (x : k) :
    x ^ a - (x ^ 2 - 1) ^ a ≠ 0 :=
  den_ne_zero (sq_ne_neg_one ha haσ) ha (a_ne_zero haσ) (fun _ => sq_eq_one_of_pow_eq_one haσ) x

theorem D3_ne_zero (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2)
    (hσ2 : ∀ x : k, σ x * x ^ 2 = 1 → x = 1) (x : k) :
    x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a) ≠ 0 :=
  den_ne_zero (sq_ne_neg_one ha haσ) (even_two.add ha) (by omega)
    (fun _ => sq_eq_one_of_pow_two_add_eq_one haσ hσ2) x

end CFSG.Walter.Ree.T2.Alg
