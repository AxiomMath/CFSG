module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux2

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

theorem owL5_braid {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {a b : U} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hra2 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1)
    (hrb2 : owCr_orthRefl Q b hb * owCr_orthRefl Q b hb = 1)
    (hord : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) = 3) :
    owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q a ha
      = owCr_orthRefl Q b hb * owCr_orthRefl Q a ha * owCr_orthRefl Q b hb := by
  set ra := owCr_orthRefl Q a ha with hra
  set rb := owCr_orthRefl Q b hb with hrb
  have hra2' : ra * ra = 1 := by rw [hra]; exact hra2
  have hrb2' : rb * rb = 1 := by rw [hrb]; exact hrb2
  have hpow : (ra * rb) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hp3 : (ra * rb) ^ 3 = ra * rb * ra * rb * ra * rb := by
    rw [pow_succ, pow_succ, pow_one]; simp only [mul_assoc]
  have key : (ra * rb * ra) * (rb * ra * rb) = 1 := by
    rw [show (ra * rb * ra) * (rb * ra * rb) = ra * rb * ra * rb * ra * rb by
      simp only [mul_assoc]]
    rw [← hp3, hpow]
  have hself : (ra * rb * ra) * (ra * rb * ra) = 1 := by
    calc (ra * rb * ra) * (ra * rb * ra)
        = ra * rb * (ra * ra) * rb * ra := by simp only [mul_assoc]
      _ = ra * rb * 1 * rb * ra := by rw [hra2']
      _ = ra * (rb * rb) * ra := by simp only [mul_assoc, mul_one]
      _ = ra * 1 * ra := by rw [hrb2']
      _ = ra * ra := by rw [mul_one]
      _ = 1 := hra2'
  have h1 : rb * ra * rb = (ra * rb * ra)⁻¹ := eq_inv_of_mul_eq_one_right key
  have h2 : (ra * rb * ra)⁻¹ = ra * rb * ra := inv_eq_of_mul_eq_one_right hself
  exact (h1.trans h2).symm

theorem owL5_E1 {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {a b : U} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hbraid : owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q a ha
      = owCr_orthRefl Q b hb * owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) :
    (1 - (polarBilin Q a b / Q b) * (polarBilin Q a b / Q a)) •
      (2 • a - (polarBilin Q a b / Q b) • b) = 0 := by
  set x : K := polarBilin Q a b / Q a with hx
  set y : K := polarBilin Q a b / Q b with hy
  have hba : polarBilin Q b a = polarBilin Q a b := by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]
  have hra_a : owCr_orthRefl Q a ha a = -a := owCr_orthRefl_self Q a ha
  have hrb_b : owCr_orthRefl Q b hb b = -b := owCr_orthRefl_self Q b hb
  have hra_b : owCr_orthRefl Q a ha b = b - x • a := by
    rw [owCr_orthRefl_apply, hba, ← hx]
  have hrb_a : owCr_orthRefl Q b hb a = a - y • b := by
    rw [owCr_orthRefl_apply, ← hy]
  have h := congrArg (fun f : U ≃ₗ[K] U => f a) hbraid
  have hL : (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb * owCr_orthRefl Q a ha) a
      = (1 - y * x) • a + y • b := by
    simp only [LinearEquiv.mul_apply, map_sub, map_smul, map_neg, hra_a, hra_b, hrb_a]
    module
  have hR : (owCr_orthRefl Q b hb * owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) a
      = (y * x - 1) • a + (y * (2 - y * x)) • b := by
    simp only [LinearEquiv.mul_apply, map_sub, map_smul, map_neg, hra_a, hra_b, hrb_a, hrb_b]
    module
  rw [hL, hR] at h
  have h' : (1 - y * x) • (2 • a - y • b)
      = ((1 - y * x) • a + y • b) - ((y * x - 1) • a + (y * (2 - y * x)) • b) := by
    module
  rw [h', h, sub_self]

theorem owL5_sq_polar {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {a b : U} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hra2 : owCr_orthRefl Q a ha * owCr_orthRefl Q a ha = 1)
    (hrb2 : owCr_orthRefl Q b hb * owCr_orthRefl Q b hb = 1)
    (hord : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q b hb) = 3) :
    polarBilin Q a b * polarBilin Q a b = Q a * Q b := by
  have hbraid := owL5_braid Q ha hb hra2 hrb2 hord
  have hE1 := owL5_E1 Q ha hb hbraid
  set x : K := polarBilin Q a b / Q a with hx
  set y : K := polarBilin Q a b / Q b with hy
  have hscal : (1 - y * x) * (4 * Q a - y * polarBilin Q a b) = 0 := by
    have hfun := congrArg ((polarBilin Q).flip a) hE1
    simp only [map_smul, map_zero, map_sub, map_add, map_neg, LinearMap.flip_apply,
      polarBilin_apply_apply, polar_self, polar_smul_left, smul_eq_mul, two_smul] at hfun
    have hba2 : polar Q b a = polarBilin Q a b := by
      rw [polar_comm, ← polarBilin_apply_apply]
    rw [hba2] at hfun
    convert hfun using 1 <;> ring
  have h4 : (4 : K) = 1 := by
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    rw [show (4 : K) = 3 + 1 by norm_num, h3, zero_add]
  have hkey : (1 - y * x) * (Q a - y * polarBilin Q a b) = 0 := by
    simpa [h4, one_mul] using hscal
  have hmain : (Q a * Q b - polarBilin Q a b * polarBilin Q a b) *
      (Q a * Q b - polarBilin Q a b * polarBilin Q a b) = 0 := by
    have h2 : (1 - y * x) * (Q a - y * polarBilin Q a b) * (Q a * Q b * Q b)
        = (Q a * Q b - polarBilin Q a b * polarBilin Q a b) *
          (Q a * Q b - polarBilin Q a b * polarBilin Q a b) := by
      rw [hx, hy]
      field_simp
      try ring
    rw [hkey, zero_mul] at h2
    exact h2.symm
  exact (sub_eq_zero.mp (mul_self_eq_zero.mp hmain)).symm


end CFSG.StandardType.ZS

end
