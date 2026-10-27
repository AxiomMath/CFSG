module

public import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.DivMod

public section

namespace CFSG.StandardType

open Module Polynomial.Chebyshev

@[expose] noncomputable def ggCoxA (R : Type*) [CommRing R] (m : ℤ) (t : R) : R :=
  (S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)

@[expose] noncomputable def ggCoxB (R : Type*) [CommRing R] (m : ℤ) (t : R) : R :=
  (S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {x y : M} {f g : Module.Dual R M}

theorem reflection_mul_reflection_apply' (hf : f x = 2) (hg : g y = 2) (z : M) :
    (reflection hf * reflection hg) z = z - g z • y - (f z - f y * g z) • x := by
  rw [LinearEquiv.mul_apply]
  simp only [reflection_apply, map_sub, map_smul]
  module

theorem reflection_mul_reflection_sq_apply_of_eq_zero (hf : f x = 2) (hg : g y = 2)
    (hfy : f y = 0) (z : M) :
    ((reflection hf * reflection hg) ^ 2) z = z + (g x * f z) • y := by
  rw [pow_two, LinearEquiv.mul_apply, reflection_mul_reflection_apply' hf hg,
    reflection_mul_reflection_apply' hf hg]
  simp only [map_sub, map_smul, smul_eq_mul, hf, hg, hfy]
  module

theorem reflection_mul_reflection_apply_of_eq_smul (hf : f x = 2) (hg : g y = 2) {c : R}
    (hy : y = c • x) (z : M) :
    (reflection hf * reflection hg) z = z + (c * g z - f z) • x := by
  rw [reflection_mul_reflection_apply' hf hg]
  subst hy
  simp only [map_smul, smul_eq_mul, hf]
  module

theorem sub_apply_self_of_eq_smul (hf : f x = 2) (hg : g y = 2) {c : R} (hy : y = c • x) :
    c * g x - f x = 0 := by
  subst hy
  rw [map_smul, smul_eq_mul] at hg
  rw [hg, hf, sub_self]

theorem reflection_mul_reflection_apply_of_eq_smul_dual (hf : f x = 2) (hg : g y = 2) {c : R}
    (hgf : g = c • f) (z : M) :
    (reflection hf * reflection hg) z = z + f z • (x - c • y) := by
  rw [reflection_mul_reflection_apply' hf hg]
  subst hgf
  simp only [LinearMap.smul_apply, smul_eq_mul] at hg ⊢
  have h2 : f y * (c * f z) = 2 * f z := by rw [← hg]; ring
  rw [h2]
  module

theorem apply_sub_smul_of_eq_smul_dual (hf : f x = 2) (hg : g y = 2) {c : R}
    (hgf : g = c • f) : f (x - c • y) = 0 := by
  subst hgf
  simp only [LinearMap.smul_apply, smul_eq_mul] at hg
  rw [map_sub, map_smul, smul_eq_mul, hf, hg, sub_self]

theorem reflection_mul_reflection_pow_apply' (hf : f x = 2) (hg : g y = 2) (m : ℕ) (z : M) :
    ((reflection hf * reflection hg) ^ m) z = z +
      (ggCoxB R m (f y * g x - 2) * f y * g z -
        (ggCoxA R m (f y * g x - 2) + ggCoxB R m (f y * g x - 2)) * f z) • x +
      (ggCoxA R m (f y * g x - 2) * g x * f z -
        (ggCoxA R m (f y * g x - 2) + ggCoxB R m (f y * g x - 2)) * g z) • y := by
  rw [reflection_mul_reflection_pow_apply hf hg m z]
  simp only [ggCoxA, ggCoxB]
  module

theorem reflection_mul_reflection_pow_eq_one_of (hf : f x = 2) (hg : g y = 2) (m : ℕ)
    (hA : ggCoxA R m (f y * g x - 2) = 0) (hB : ggCoxB R m (f y * g x - 2) = 0) :
    (reflection hf * reflection hg) ^ m = 1 := by
  refine LinearEquiv.ext fun z => ?_
  rw [reflection_mul_reflection_pow_apply' hf hg m z, hA, hB]
  simp

theorem reflection_mul_reflection_pow_eq_one_iff (hf : f x = 2) (hg : g y = 2)
    (hxy : LinearIndependent R ![x, y]) (hfg : LinearIndependent R ![f, g]) (m : ℕ) :
    (reflection hf * reflection hg) ^ m = 1 ↔
      ggCoxA R m (f y * g x - 2) + ggCoxB R m (f y * g x - 2) = 0 ∧
        f y * ggCoxB R m (f y * g x - 2) = 0 ∧ g x * ggCoxA R m (f y * g x - 2) = 0 := by
  set A := ggCoxA R m (f y * g x - 2) with hA
  set B := ggCoxB R m (f y * g x - 2) with hB
  constructor
  · intro h
    have hz : ∀ z : M, (B * f y * g z - (A + B) * f z) • x +
        (A * g x * f z - (A + B) * g z) • y = 0 := by
      intro z
      have hz := reflection_mul_reflection_pow_apply' hf hg m z
      rw [h, LinearEquiv.coe_one, id, add_assoc, left_eq_add] at hz
      exact hz
    have hc := fun z => LinearIndependent.pair_iff.mp hxy _ _ (hz z)
    have h1 : (-(A + B)) • f + (B * f y) • g = 0 := by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      linear_combination (hc z).1
    have h2 : (A * g x) • f + (-(A + B)) • g = 0 := by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      linear_combination (hc z).2
    obtain ⟨e1, e2⟩ := LinearIndependent.pair_iff.mp hfg _ _ h1
    obtain ⟨e3, -⟩ := LinearIndependent.pair_iff.mp hfg _ _ h2
    exact ⟨neg_eq_zero.mp e1, by rw [mul_comm]; exact e2, by rw [mul_comm]; exact e3⟩
  · rintro ⟨h1, h2, h3⟩
    refine LinearEquiv.ext fun z => ?_
    rw [reflection_mul_reflection_pow_apply' hf hg m z, ← hA, ← hB, h1,
      mul_comm B, h2, mul_comm A, h3]
    simp

theorem ggCoxA_two_mul (k : ℤ) (t : R) :
    ggCoxA R (2 * k) t = (S R (k - 1)).eval t * ((S R (k - 1)).eval t + (S R (k - 2)).eval t) := by
  simp only [ggCoxA]
  rw [show (2 * k - 2) / 2 = k - 1 by omega, show (2 * k - 1) / 2 = k - 1 by omega,
    show (2 * k - 3) / 2 = k - 2 by omega]

theorem ggCoxB_two_mul (k : ℤ) (t : R) :
    ggCoxB R (2 * k) t = (S R (k - 1)).eval t * ((S R k).eval t + (S R (k - 1)).eval t) := by
  simp only [ggCoxB]
  rw [show (2 * k - 1) / 2 = k - 1 by omega, show 2 * k / 2 = k by omega,
    show (2 * k - 2) / 2 = k - 1 by omega]

theorem ggCoxA_two_mul_add_one (k : ℤ) (t : R) :
    ggCoxA R (2 * k + 1) t = (S R (k - 1)).eval t * ((S R k).eval t + (S R (k - 1)).eval t) := by
  simp only [ggCoxA]
  rw [show (2 * k + 1 - 2) / 2 = k - 1 by omega, show (2 * k + 1 - 1) / 2 = k by omega,
    show (2 * k + 1 - 3) / 2 = k - 1 by omega]

theorem ggCoxB_two_mul_add_one (k : ℤ) (t : R) :
    ggCoxB R (2 * k + 1) t = (S R k).eval t * ((S R k).eval t + (S R (k - 1)).eval t) := by
  simp only [ggCoxB]
  rw [show (2 * k + 1 - 1) / 2 = k by omega, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1 - 2) / 2 = k - 1 by omega]

theorem reflection_mul_reflection_pow_even_eq_one (hf : f x = 2) (hg : g y = 2) (k : ℕ)
    (h : (S R ((k : ℤ) - 1)).eval (f y * g x - 2) = 0) :
    (reflection hf * reflection hg) ^ (2 * k) = 1 := by
  refine reflection_mul_reflection_pow_eq_one_of hf hg _ ?_ ?_
  · rw [Nat.cast_mul, Nat.cast_two, ggCoxA_two_mul, h, zero_mul]
  · rw [Nat.cast_mul, Nat.cast_two, ggCoxB_two_mul, h, zero_mul]

theorem reflection_mul_reflection_pow_odd_eq_one (hf : f x = 2) (hg : g y = 2) (k : ℕ)
    (h : (S R k).eval (f y * g x - 2) + (S R ((k : ℤ) - 1)).eval (f y * g x - 2) = 0) :
    (reflection hf * reflection hg) ^ (2 * k + 1) = 1 := by
  refine reflection_mul_reflection_pow_eq_one_of hf hg _ ?_ ?_
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one, ggCoxA_two_mul_add_one, h,
      mul_zero]
  · rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one, ggCoxB_two_mul_add_one, h,
      mul_zero]

theorem reflection_mul_reflection_pow_two (hf : f x = 2) (hg : g y = 2) (hfy : f y = 0)
    (hgx : g x = 0) : (reflection hf * reflection hg) ^ 2 = 1 := by
  refine LinearEquiv.ext fun z => ?_
  rw [reflection_mul_reflection_sq_apply_of_eq_zero hf hg hfy, hgx, zero_mul, zero_smul,
    add_zero]
  rfl

theorem reflection_mul_reflection_pow_three (hf : f x = 2) (hg : g y = 2) (h : f y * g x = 1) :
    (reflection hf * reflection hg) ^ 3 = 1 := by
  refine reflection_mul_reflection_pow_odd_eq_one hf hg 1 ?_
  rw [h, Nat.cast_one, sub_self, S_one, S_zero, Polynomial.eval_X, Polynomial.eval_one]
  ring

theorem reflection_mul_reflection_pow_four (hf : f x = 2) (hg : g y = 2) (h : f y * g x = 2) :
    (reflection hf * reflection hg) ^ 4 = 1 := by
  refine reflection_mul_reflection_pow_even_eq_one hf hg 2 ?_
  rw [h, show ((2 : ℕ) : ℤ) - 1 = 1 by norm_num, S_one, Polynomial.eval_X, sub_self]

theorem reflection_mul_reflection_pow_six (hf : f x = 2) (hg : g y = 2) (h : f y * g x = 3) :
    (reflection hf * reflection hg) ^ 6 = 1 := by
  refine reflection_mul_reflection_pow_even_eq_one hf hg 3 ?_
  rw [h, show ((3 : ℕ) : ℤ) - 1 = 2 by norm_num, S_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  ring

theorem reflection_mul_reflection_pow_char (hf : f x = 2) (hg : g y = 2) {p : ℕ} [CharP R p]
    (hp : Odd p) (h : f y * g x = 4) : (reflection hf * reflection hg) ^ p = 1 := by
  obtain ⟨k, rfl⟩ := hp
  refine reflection_mul_reflection_pow_odd_eq_one hf hg k ?_
  have ht : f y * g x - 2 = 2 := by rw [h]; norm_num
  rw [ht, S_eval_two, S_eval_two]
  have hc := CharP.cast_eq_zero R (2 * k + 1)
  push_cast at hc ⊢
  linear_combination hc

end Ring

section Field

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  {x y : M} {f g : Module.Dual K M}

theorem reflection_mul_reflection_pow_eq_one_iff_of_ne_zero (hf : f x = 2) (hg : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (hfg : LinearIndependent K ![f, g]) (hu : f y ≠ 0)
    (hv : g x ≠ 0) (m : ℕ) :
    (reflection hf * reflection hg) ^ m = 1 ↔
      ggCoxA K m (f y * g x - 2) = 0 ∧ ggCoxB K m (f y * g x - 2) = 0 := by
  rw [reflection_mul_reflection_pow_eq_one_iff hf hg hxy hfg]
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨(mul_eq_zero.mp h3).resolve_left hv, (mul_eq_zero.mp h2).resolve_left hu⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem reflection_mul_reflection_pow_even_eq_one_iff (hf : f x = 2) (hg : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (hfg : LinearIndependent K ![f, g]) (hu : f y ≠ 0)
    (hv : g x ≠ 0) (k : ℕ) :
    (reflection hf * reflection hg) ^ (2 * k) = 1 ↔
      (S K ((k : ℤ) - 1)).eval (f y * g x - 2) = 0 := by
  rw [reflection_mul_reflection_pow_eq_one_iff_of_ne_zero hf hg hxy hfg hu hv]
  push_cast
  rw [ggCoxA_two_mul, ggCoxB_two_mul]
  constructor
  · rintro ⟨hA, hB⟩
    by_contra h0
    have e1 := (mul_eq_zero.mp hA).resolve_left h0
    have e2 := (mul_eq_zero.mp hB).resolve_left h0
    have hrec : (S K (k : ℤ)).eval (f y * g x - 2) = (f y * g x - 2) *
        (S K ((k : ℤ) - 1)).eval (f y * g x - 2) - (S K ((k : ℤ) - 2)).eval (f y * g x - 2) := by
      have := congrArg (Polynomial.eval (f y * g x - 2)) (S_eq K (k : ℤ))
      simpa using this
    have h3 : (f y * g x) * (S K ((k : ℤ) - 1)).eval (f y * g x - 2) = 0 := by
      linear_combination e1 + e2 - hrec
    exact h0 ((mul_eq_zero.mp h3).resolve_left (mul_ne_zero hu hv))
  · intro h
    exact ⟨by rw [h, zero_mul], by rw [h, zero_mul]⟩

theorem reflection_mul_reflection_pow_odd_eq_one_iff (hf : f x = 2) (hg : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (hfg : LinearIndependent K ![f, g]) (hu : f y ≠ 0)
    (hv : g x ≠ 0) (k : ℕ) :
    (reflection hf * reflection hg) ^ (2 * k + 1) = 1 ↔
      (S K k).eval (f y * g x - 2) + (S K ((k : ℤ) - 1)).eval (f y * g x - 2) = 0 := by
  rw [reflection_mul_reflection_pow_eq_one_iff_of_ne_zero hf hg hxy hfg hu hv]
  push_cast
  rw [ggCoxA_two_mul_add_one, ggCoxB_two_mul_add_one]
  constructor
  · rintro ⟨hA, hB⟩
    by_contra h0
    have e1 := (mul_eq_zero.mp hA).resolve_right h0
    have e2 := (mul_eq_zero.mp hB).resolve_right h0
    have h1 := congrArg (Polynomial.eval (f y * g x - 2)) (S_sq_add_S_sq K ((k : ℤ) - 1))
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one, sub_add_cancel, e1, e2] at h1
    norm_num at h1
  · intro h
    exact ⟨by rw [h, mul_zero], by rw [h, mul_zero]⟩

theorem orderOf_reflection_mul_reflection_eq {M' : Type*} [AddCommGroup M'] [Module K M']
    {x' y' : M'} {f' g' : Module.Dual K M'} (hf : f x = 2) (hg : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (hfg : LinearIndependent K ![f, g]) (hu : f y ≠ 0)
    (hv : g x ≠ 0) (hf' : f' x' = 2) (hg' : g' y' = 2) (hxy' : LinearIndependent K ![x', y'])
    (hfg' : LinearIndependent K ![f', g']) (hu' : f' y' ≠ 0) (hv' : g' x' ≠ 0)
    (huv : f y * g x = f' y' * g' x') :
    orderOf (reflection hf * reflection hg) = orderOf (reflection hf' * reflection hg') := by
  rw [orderOf_eq_orderOf_iff]
  intro m
  rw [reflection_mul_reflection_pow_eq_one_iff_of_ne_zero hf hg hxy hfg hu hv,
    reflection_mul_reflection_pow_eq_one_iff_of_ne_zero hf' hg' hxy' hfg' hu' hv', huv]

theorem exists_eq_smul_of_not_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
    {a b : V} (ha : a ≠ 0) (h : ¬ LinearIndependent K ![a, b]) : ∃ c : K, b = c • a := by
  rw [LinearIndependent.pair_iff' ha] at h
  push Not at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

theorem linearIndependent_and_or_exists_transvection [NeZero (2 : K)] (hf : f x = 2)
    (hg : g y = 2) :
    (LinearIndependent K ![x, y] ∧ LinearIndependent K ![f, g]) ∨
      ∃ (w : M) (φ : Module.Dual K M), φ w = 0 ∧
        ∀ z, (reflection hf * reflection hg) z = z + φ z • w := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact two_ne_zero hf.symm
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [LinearMap.zero_apply] at hf
    exact two_ne_zero hf.symm
  by_cases hxy : LinearIndependent K ![x, y]
  · by_cases hfg : LinearIndependent K ![f, g]
    · exact Or.inl ⟨hxy, hfg⟩
    · obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent hf0 hfg
      exact Or.inr ⟨x - c • y, f, apply_sub_smul_of_eq_smul_dual hf hg hc,
        reflection_mul_reflection_apply_of_eq_smul_dual hf hg hc⟩
  · obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent hx hxy
    refine Or.inr ⟨x, c • g - f, ?_, fun z => ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      exact sub_apply_self_of_eq_smul hf hg hc
    · rw [reflection_mul_reflection_apply_of_eq_smul hf hg hc]
      simp

end Field

end CFSG.StandardType
