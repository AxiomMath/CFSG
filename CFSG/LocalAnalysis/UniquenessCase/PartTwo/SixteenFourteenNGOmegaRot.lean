module

public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem s1614_rt_neg_eq [CharP K 2] (x : V) : -x = x := by
  rw [← neg_one_smul K x, CharTwo.neg_eq, one_smul]

private theorem s1614_rt_sub_eq_add [CharP K 2] (x y : V) : x - y = x + y := by
  rw [sub_eq_add_neg, s1614_rt_neg_eq (K := K)]

private theorem s1614_rt_add_self_eq_zero [CharP K 2] (x : V) : x + x = 0 := by
  rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]

private theorem s1614_rt_reflect_apply_of_map_eq_one [CharP K 2] {Q : QuadraticForm K V} {v : V}
    (hv : Q v = 1) (x : V) : reflect Q v x = x + polar Q x v • v := by
  rw [reflect_apply (by rw [hv]; exact one_ne_zero), hv, div_one, s1614_rt_sub_eq_add (K := K),
    polar_comm Q v x]

private theorem s1614_rt_commute_reflect_of_polar_eq_zero {Q : QuadraticForm K V} {u w : V}
    (h : polar Q u w = 0) : Commute (reflect Q u) (reflect Q w) := by
  have hh := reflect_conj (reflect_mem_orthogonalGroup Q u) w
  rw [reflect_apply_of_polar_eq_zero h] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

@[expose] noncomputable def s1614_rot (Q : QuadraticForm K V) (a a' : V) : V ≃ₗ[K] V :=
  reflect Q a * reflect Q a'

theorem s1614_rot_apply_left [CharP K 2] {Q : QuadraticForm K V} {a a' : V} (ha : Q a = 1)
    (ha' : Q a' = 1) (h : polar Q a a' = 1) : s1614_rot Q a a' a = a' := by
  have haa : polar Q a a = 0 := by rw [polar_self, ha, CharTwo.two_nsmul]
  have h1 : reflect Q a' a = a + a' := by
    rw [s1614_rt_reflect_apply_of_map_eq_one ha' a, h, one_smul]
  have h2 : reflect Q a (a + a') = a' := by
    rw [s1614_rt_reflect_apply_of_map_eq_one ha (a + a'), polar_add_left,
      polar_comm Q a' a, haa, h, zero_add, one_smul]
    rw [add_assoc, add_comm a' a, ← add_assoc, s1614_rt_add_self_eq_zero (K := K), zero_add]
  rw [s1614_rot, LinearEquiv.mul_apply, h1, h2]

theorem s1614_rot_apply_right [CharP K 2] {Q : QuadraticForm K V} {a a' : V} (ha : Q a = 1)
    (ha' : Q a' = 1) (h : polar Q a a' = 1) : s1614_rot Q a a' a' = a + a' := by
  have ha'a' : polar Q a' a' = 0 := by rw [polar_self, ha', CharTwo.two_nsmul]
  have h1 : reflect Q a' a' = a' := by
    rw [s1614_rt_reflect_apply_of_map_eq_one ha' a', ha'a', zero_smul, add_zero]
  rw [s1614_rot, LinearEquiv.mul_apply, h1, s1614_rt_reflect_apply_of_map_eq_one ha a',
    polar_comm Q a' a, h, one_smul, add_comm]

theorem s1614_rot_apply_of_polar_eq_zero {Q : QuadraticForm K V} {a a' v : V}
    (h : polar Q a v = 0) (h' : polar Q a' v = 0) : s1614_rot Q a a' v = v := by
  rw [s1614_rot, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero h',
    reflect_apply_of_polar_eq_zero h]

theorem s1614_rot_pow_three [CharP K 2] {Q : QuadraticForm K V} {a a' : V} (ha : Q a = 1)
    (ha' : Q a' = 1) (h : polar Q a a' = 1) : s1614_rot Q a a' ^ 3 = 1 := by
  have e1 : reflect Q a * reflect Q a' * reflect Q a = reflect Q (a + a') := by
    have hh := reflect_conj (reflect_mem_orthogonalGroup Q a) a'
    rw [reflect_inv, s1614_rt_reflect_apply_of_map_eq_one ha a', polar_comm Q a' a, h,
      one_smul, add_comm] at hh
    exact hh
  have e2 : reflect Q a' * reflect Q a * reflect Q a' = reflect Q (a + a') := by
    have hh := reflect_conj (reflect_mem_orthogonalGroup Q a') a
    rw [reflect_inv, s1614_rt_reflect_apply_of_map_eq_one ha' a, h, one_smul] at hh
    exact hh
  calc (s1614_rot Q a a') ^ 3
      = (reflect Q a * reflect Q a' * reflect Q a) *
          (reflect Q a' * reflect Q a * reflect Q a') := by
        rw [s1614_rot, pow_three]
        simp only [mul_assoc]
    _ = 1 := by rw [e1, e2, reflect_mul_self]

theorem s1614_rot_mem_commutator [CharP K 2] {Q : QuadraticForm K V} {a a' : V} (ha : Q a = 1)
    (ha' : Q a' = 1) (h : polar Q a a' = 1) :
    s1614_rot Q a a' ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hcomm : ⁅reflect Q a, reflect Q a'⁆ = s1614_rot Q a a' ^ 2 := by
    rw [commutatorElement_def, reflect_inv, reflect_inv, s1614_rot, pow_two]
    simp only [mul_assoc]
  have hρ3 : s1614_rot Q a a' ^ 3 = 1 := s1614_rot_pow_three ha ha' h
  have hmem : s1614_rot Q a a' ^ 2 ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q a)
      (reflect_mem_orthogonalGroup Q a')
  have hρeq : s1614_rot Q a a' = (s1614_rot Q a a' ^ 2) ^ 2 := by
    rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hρ3, one_mul]
  rw [hρeq]
  exact pow_mem hmem 2

theorem s1614_rot_commute {Q : QuadraticForm K V} {a a' x x' : V} (hax : polar Q a x = 0)
    (hax' : polar Q a x' = 0) (ha'x : polar Q a' x = 0) (ha'x' : polar Q a' x' = 0) :
    Commute (s1614_rot Q a a') (s1614_rot Q x x') := by
  have h1 : Commute (reflect Q a) (reflect Q x) := s1614_rt_commute_reflect_of_polar_eq_zero hax
  have h2 : Commute (reflect Q a) (reflect Q x') :=
    s1614_rt_commute_reflect_of_polar_eq_zero hax'
  have h3 : Commute (reflect Q a') (reflect Q x) :=
    s1614_rt_commute_reflect_of_polar_eq_zero ha'x
  have h4 : Commute (reflect Q a') (reflect Q x') :=
    s1614_rt_commute_reflect_of_polar_eq_zero ha'x'
  rw [s1614_rot]
  exact (h1.mul_right h2).mul_left (h3.mul_right h4)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
