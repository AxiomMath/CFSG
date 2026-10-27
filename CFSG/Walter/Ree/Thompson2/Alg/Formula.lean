module

public import CFSG.Walter.Ree.Thompson2.Alg.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Walter.Ree.T2.Alg

variable {k : Type} [Field k]

@[expose] def s1F (a : ℕ) (x : k) : k := ((x - 1) ^ a - x ^ a) / (x ^ a - (x ^ 2 - 1) ^ a)

@[expose] def c2F (σ : k ≃+* k) (a : ℕ) (t : k) : k := s1F a t - σ (s1F a t)

@[expose] def s2F (σ : k ≃+* k) (a : ℕ) (x : k) : k :=
  ((x - 1) * (x ^ 2 + x - 1) + x ^ 2 * c2F σ a (ι₂ x) - (x - 1) ^ 2 * c2F σ a (-x⁻¹)) /
    -((x ^ 2 - x - 1) * (x ^ 2 + x - 1))

@[expose] def c3F (σ : k ≃+* k) (a : ℕ) (d t : k) : k :=
  1 - d - s2F σ a t - σ (s1F a t) - s1F a t + s1F a t ^ 2

@[expose] def phi3 (a : ℕ) (x : k) : k := s1F (2 + a) x

@[expose] def s3F (σ : k ≃+* k) (a : ℕ) (d x : k) : k :=
  (x ^ (2 + a) * c3F σ a d (ι₂ x) - (x - 1) ^ (2 + a) * c3F σ a d (-x⁻¹)) /
    (x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a))

open Classical in
@[expose] noncomputable def sFormula (σ : k ≃+* k) (a : ℕ) (d x : k) : k × k × k :=
  (s1F a x, s2F σ a x, if x ^ 3 = x then 1 + d * phi3 a x else s3F σ a d x)

@[expose] noncomputable def psi3 (σ : k ≃+* k) (a : ℕ) (x : k) : k := (sFormula σ a 0 x).2.2

variable {σ : k ≃+* k} {a : ℕ}

theorem sFormula_thd (d x : k) : (sFormula σ a d x).2.2 = psi3 σ a x + d * phi3 a x := by
  rw [psi3, sFormula, sFormula]
  split_ifs
  · ring
  · rw [show phi3 a x = ((x - 1) ^ (2 + a) - x ^ (2 + a)) / (x ^ (2 + a) - (x ^ 2 - 1) ^ (2 + a))
      from rfl]
    simp only [s3F, c3F]
    ring

theorem s1F_one {e : ℕ} (he0 : e ≠ 0) : s1F e (1 : k) = -1 := by
  norm_num [s1F, zero_pow he0]

theorem s1F_zero {e : ℕ} (he : Even e) (he0 : e ≠ 0) : s1F e (0 : k) = -1 := by
  norm_num [s1F, zero_pow he0, he.neg_one_pow]

theorem c2F_zero (ha : Even a) (ha0 : a ≠ 0) : c2F σ a (0 : k) = 0 := by
  rw [c2F, s1F_zero ha ha0, map_neg, map_one, sub_neg_eq_add, neg_add_cancel]

theorem c2F_one (ha0 : a ≠ 0) : c2F σ a (1 : k) = 0 := by
  rw [c2F, s1F_one ha0, map_neg, map_one, sub_neg_eq_add, neg_add_cancel]

variable [CharP k 3]

theorem s1F_neg_one {e : ℕ} (he : Even e) : s1F e (-1 : k) = 0 := by
  rw [s1F, neg_one_sub_one, one_pow, he.neg_one_pow, sub_self, zero_div]

theorem c2F_neg_one (ha : Even a) : c2F σ a (-1 : k) = 0 := by
  rw [c2F, s1F_neg_one ha, map_zero, sub_zero]

theorem s2F_neg_one (ha : Even a) (ha0 : a ≠ 0) : s2F σ a (-1 : k) = -1 := by
  have h : ι₂ (-1 : k) = 0 := by simp [ι₂]
  rw [s2F, h, show -(-1 : k)⁻¹ = 1 by norm_num, c2F_zero ha ha0, c2F_one ha0]
  norm_num
  linear_combination three_eq_zero (k := k)

theorem s2F_zero (ha : Even a) (ha0 : a ≠ 0) : s2F σ a (0 : k) = -1 := by
  have h : ι₂ (0 : k) = -1 := by simp [ι₂]
  rw [s2F, h, inv_zero, neg_zero, c2F_zero ha ha0, c2F_neg_one ha]
  norm_num

theorem s2F_one (ha : Even a) (ha0 : a ≠ 0) : s2F σ a (1 : k) = 0 := by
  have h : ι₂ (1 : k) = 0 := by simp [ι₂]
  rw [s2F, h, inv_one, c2F_zero ha ha0, c2F_neg_one ha]
  norm_num

end CFSG.Walter.Ree.T2.Alg
