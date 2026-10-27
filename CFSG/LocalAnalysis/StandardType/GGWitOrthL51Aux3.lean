module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthL51Aux2

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

theorem owL5_four {K : Type*} [Field K] [CharP K 3] : (4 : K) = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [show (4 : K) = 3 + 1 by norm_num, h3, zero_add]

theorem owL5_neg_two {K : Type*} [Field K] [CharP K 3] : (-2 : K) = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h : (-2 : K) - 1 = 0 := by
    rw [show (-2 : K) - 1 = -(3 : K) by ring, h3, neg_zero]
  exact sub_eq_zero.mp h

theorem owL5_polar_symm {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) (x y : U) : polarBilin Q x y = polarBilin Q y x := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_comm]

theorem owL5_Q_neg {K : Type*} [Field K] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {u : U} (hu : Q u = 0) : Q (-u) = 0 := by
  rw [QuadraticMap.map_neg, hu]

theorem owL5_two {K : Type*} [Field K] [CharP K 3] : (2 : K) = -1 := by
  have := owL5_neg_two (K := K)
  rw [show (2 : K) = -(-2) by ring, this]

theorem owL5_two_ne_zero {K : Type*} [Field K] [CharP K 3] : (2 : K) ≠ 0 := by
  intro h2
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add] at h3
  exact one_ne_zero h3

theorem owL5_two_smul {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U]
    [Module K U] (v : U) : (2 : K) • v = -v := by rw [owL5_two, neg_smul, one_smul]

theorem owL5_neg_two_smul {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U]
    [Module K U] (v : U) : (-2 : K) • v = v := by rw [owL5_neg_two, one_smul]


theorem owL5_conj {K : Type*} [Field K] [CharP K 3] {U : Type} [AddCommGroup U] [Module K U]
    (Q : QuadraticForm K U) {a u' : U} (ha : Q a ≠ 0) (hu' : Q u' = 0)
    (hau' : polarBilin Q u' a = 0)
    (h1 : Q (a - u') ≠ 0) (h2 : Q ((2 : K) • a - u') ≠ 0) :
    owCr_orthRefl Q ((2 : K) • a - u') h2 * owCr_orthRefl Q a ha *
      (owCr_orthRefl Q ((2 : K) • a - u') h2)⁻¹ = owCr_orthRefl Q (a - u') h1 := by
  have h4 : (4 : K) = 1 := owL5_four
  have hden : Q ((2 : K) • a - u') = Q a := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q ((2 : K) • a) (-u')
      (by rw [QuadraticMap.map_neg, hu'])
      (by rw [polarBilin_apply_apply, polar_neg_left, polar_smul_right,
        ← polarBilin_apply_apply, hau']; ring)]
    rw [QuadraticMap.map_smul, smul_eq_mul, show (2 : K) * 2 = 4 by ring, h4, one_mul]
  have hga : owCr_orthRefl Q ((2 : K) • a - u') h2 a = -(a - u') := by
    rw [owCr_orthRefl_apply]
    have hnum : polarBilin Q a ((2 : K) • a - u') = 4 * Q a := by
      rw [polarBilin_apply_apply, polar_sub_right, polar_smul_right, polar_self,
        smul_eq_mul, polar_comm, ← polarBilin_apply_apply, hau']
      ring
    rw [hnum, hden, h4, one_mul]
    rw [div_self ha, one_smul]
    module
  have hgane : Q (owCr_orthRefl Q ((2 : K) • a - u') h2 a) ≠ 0 := by
    rw [hga, QuadraticMap.map_neg]; exact h1
  have hnegp : Q (-(a - u')) ≠ 0 := by rw [QuadraticMap.map_neg]; exact h1
  rw [owCr_orthRefl_conj Q (owCr_orthRefl Q ((2 : K) • a - u') h2)
    (fun v => owCr_orthRefl_isIsom Q ((2 : K) • a - u') h2 v) a ha hgane]
  simpa only [hga] using owCr_orthRefl_neg Q (a - u') h1 hnegp

theorem owL5_not_commute {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u' : U} (ha : Q a ≠ 0)
    (hu0 : u' ≠ 0) (hu' : Q u' = 0) (hau' : polarBilin Q u' a = 0)
    (h1 : Q (a - u') ≠ 0) :
    ¬ Commute (owCr_orthRefl Q (a - u') h1) (owCr_orthRefl Q a ha) := by
  have haa : polar Q a a = 2 * Q a := by rw [polar_self, two_smul]; ring
  have hau'_p : polar Q a u' = 0 := by rw [polar_comm, ← polarBilin_apply_apply, hau']
  have hnum : polarBilin Q a (a - u') = 2 * Q a := by
    rw [polarBilin_apply_apply, polar_sub_right, haa, hau'_p, sub_zero]
  have hnum2 : polarBilin Q (-a - u') a = -2 * Q a := by
    rw [polarBilin_apply_apply, polar_sub_left, polar_neg_left, haa, ← polarBilin_apply_apply,
      hau', sub_zero]
    ring
  have hden : Q (a - u') = Q a := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q a (-u') (owL5_Q_neg Q hu')
      (by rw [polarBilin_apply_apply, polar_neg_left, ← polarBilin_apply_apply, hau', neg_zero])]
  intro hc
  have h := congrArg (fun f : U ≃ₗ[K] U => f a) hc
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  have hra_a : owCr_orthRefl Q a ha a = -a := owCr_orthRefl_self Q a ha
  have hra_u' : owCr_orthRefl Q a ha u' = u' := by
    rw [owCr_orthRefl_apply, hau', zero_div, zero_smul, sub_zero]
  have hta : owCr_orthRefl Q (a - u') h1 a = -a - u' := by
    rw [owCr_orthRefl_apply, hnum, hden, mul_div_cancel_right₀ _ ha]
    have h2a : (2 : K) • a = -a := owL5_two_smul a
    have h2m : (2 : K) • (a - u') = -(a - u') := owL5_two_smul (a - u')
    rw [h2m, ← h2a]
    module
  have hra_ta : owCr_orthRefl Q a ha (-a - u') = a - u' := by
    rw [show -a - u' = -a + -u' by abel, map_add, map_neg, map_neg, hra_a, hra_u']
    abel
  rw [hra_a, map_neg, hta, hra_ta] at h
  have h2u : (2 : K) • u' = 0 := by
    have hh := h
    rw [show -(-a - u') = a + u' by abel] at hh
    have h1' : u' = -u' := by
      have := hh
      rw [sub_eq_add_neg] at this
      exact add_left_cancel this
    rw [two_smul]
    nth_rewrite 2 [h1']
    exact add_neg_cancel u'
  exact (smul_ne_zero owL5_two_ne_zero hu0) h2u

theorem owL5_form_a {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0) (x y z : K) :
    owCr_orthRefl Q a ha (x • a + y • u + z • u') = (-x) • a + y • u + z • u' := by
  have haa : polar Q a a = 2 * Q a := by rw [polar_self, two_smul]; ring
  have hua : polar Q u a = 0 := by rw [← polarBilin_apply_apply, hau]
  have hu'a : polar Q u' a = 0 := by rw [← polarBilin_apply_apply, hau']
  rw [owCr_orthRefl_apply]
  have hnum : polarBilin Q (x • a + y • u + z • u') a = 2 * x * Q a := by
    simp only [polarBilin_apply_apply, polar_add_left, polar_smul_left, smul_eq_mul, haa, hua,
      hu'a, mul_zero, add_zero]
    ring
  rw [hnum, show (2 * x * Q a / Q a) = 2 * x by rw [mul_div_cancel_right₀ (2 * x) ha]]
  module

theorem owL5_form_au {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hbu : Q (a - u) ≠ 0) (x y z : K) :
    owCr_orthRefl Q (a - u) hbu (x • a + y • u + z • u')
      = (-x) • a + (y + 2 * x) • u + z • u' := by
  have haa : polar Q a a = 2 * Q a := by rw [polar_self, two_smul]; ring
  have hua : polar Q u a = 0 := by rw [← polarBilin_apply_apply, hau]
  have hu'a : polar Q u' a = 0 := by rw [← polarBilin_apply_apply, hau']
  have huu : polar Q u u = 0 := by rw [polar_self, two_smul, hu]; ring
  have hu'u : polar Q u' u = 0 := by rw [← polarBilin_apply_apply, huu']
  have haup : polar Q a u = 0 := by rw [polar_comm, hua]
  have hden : Q (a - u) = Q a := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q a (-u) (owL5_Q_neg Q hu)
      (by rw [polarBilin_apply_apply, polar_neg_left, ← polarBilin_apply_apply, hau, neg_zero])]
  rw [owCr_orthRefl_apply]
  have hnum : polarBilin Q (x • a + y • u + z • u') (a - u) = 2 * x * Q a := by
    simp only [polarBilin_apply_apply, polar_sub_right, polar_add_left, polar_smul_left,
      smul_eq_mul, haa, hua, hu'a, huu, hu'u, haup, mul_zero, add_zero, sub_zero]
    ring
  rw [hnum, hden, show (2 * x * Q a / Q a) = 2 * x by rw [mul_div_cancel_right₀ (2 * x) ha]]
  module

theorem owL5_form_au' {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hbu' : Q (a - u') ≠ 0) (x y z : K) :
    owCr_orthRefl Q (a - u') hbu' (x • a + y • u + z • u')
      = (-x) • a + y • u + (z + 2 * x) • u' := by
  have haa : polar Q a a = 2 * Q a := by rw [polar_self, two_smul]; ring
  have hua : polar Q u a = 0 := by rw [← polarBilin_apply_apply, hau]
  have hu'a : polar Q u' a = 0 := by rw [← polarBilin_apply_apply, hau']
  have huu'p : polar Q u u' = 0 := by rw [polar_comm, ← polarBilin_apply_apply, huu']
  have hu'u' : polar Q u' u' = 0 := by rw [polar_self, two_smul, hu']; ring
  have haup' : polar Q a u' = 0 := by rw [polar_comm, hu'a]
  have hden : Q (a - u') = Q a := by
    rw [sub_eq_add_neg, owCr_Q_add_eq Q a (-u') (owL5_Q_neg Q hu')
      (by rw [polarBilin_apply_apply, polar_neg_left, ← polarBilin_apply_apply, hau', neg_zero])]
  rw [owCr_orthRefl_apply]
  have hnum : polarBilin Q (x • a + y • u + z • u') (a - u') = 2 * x * Q a := by
    simp only [polarBilin_apply_apply, polar_sub_right, polar_add_left, polar_smul_left,
      smul_eq_mul, haa, hua, hu'a, huu'p, hu'u', haup', mul_zero, add_zero, sub_zero]
    ring
  rw [hnum, hden, show (2 * x * Q a / Q a) = 2 * x by rw [mul_div_cancel_right₀ (2 * x) ha]]
  module

theorem owL5_linearIndependent {K : Type*} [Field K] [CharP K 3] {U : Type}
    [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) {a u u' : U}
    (ha : Q a ≠ 0) (hu : Q u = 0) (hu' : Q u' = 0) (hau : polarBilin Q u a = 0)
    (hau' : polarBilin Q u' a = 0) (huu' : polarBilin Q u' u = 0)
    (hu0 : u ≠ 0) (hspan : u' ∉ Submodule.span K {u}) :
    LinearIndependent K ![a, u, u'] := by
  have gaa : polarBilin Q a a = 2 * Q a := by
    rw [polarBilin_apply_apply, polar_self, two_smul]; ring
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hg
  have hx : g 0 = 0 := by
    have h := congrArg ((polarBilin Q).flip a) hg
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
      LinearMap.zero_apply, smul_eq_mul, gaa, hau, hau', mul_zero, add_zero] at h
    have h2 : (2 * Q a) * g 0 = 0 := by simpa [mul_comm] using h
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (owL5_two_ne_zero) ha)
  have hz : g 2 = 0 := by
    by_contra hz
    apply hspan
    rw [Submodule.mem_span_singleton]
    refine ⟨-(g 2)⁻¹ * g 1, ?_⟩
    have h1 : g 2 • u' = -(g 1 • u) := by
      have h := hg
      rw [hx, zero_smul, zero_add] at h
      exact eq_neg_of_add_eq_zero_right h
    have hcalc : u' = (-(g 2)⁻¹ * g 1) • u := by
      calc u' = (g 2)⁻¹ • (g 2 • u') := by rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
        _ = (g 2)⁻¹ • (-(g 1 • u)) := by rw [h1]
        _ = (-(g 2)⁻¹ * g 1) • u := by rw [smul_neg, smul_smul, ← neg_smul, neg_mul]
    exact hcalc.symm
  have hy : g 1 = 0 := by
    have h : g 1 • u = 0 := by
      have h := hg
      rw [hx, hz, zero_smul, zero_smul, zero_add, add_zero] at h
      exact h
    exact (smul_eq_zero.mp h).resolve_right hu0
  intro i
  fin_cases i <;> simp [hx, hy, hz]

end CFSG.StandardType.ZS

end
