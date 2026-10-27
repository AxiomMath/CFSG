module

public import CFSG.ClassicalGroups.Orthogonal.CharTwo

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_smul {c : K} (hc : c ≠ 0) (v : V) : reflect Q (c • v) = reflect Q v := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv,
      reflect_of_map_eq_zero (by rw [map_smul_eq_sq, hv, mul_zero])]
  · have hcv : Q (c • v) ≠ 0 := by
      rw [map_smul_eq_sq]
      exact mul_ne_zero (pow_ne_zero 2 hc) hv
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply hcv, reflect_apply hv, polar_smul_left_eq, map_smul_eq_sq, smul_smul]
    congr 2
    field_simp

theorem reflect_add_apply (h2 : (2 : K) = 0) {x y : V} (hxy : Q x = Q y)
    (hpol : polar Q x y ≠ 0) : reflect Q (x + y) x = y := by
  have hQ : Q (x + y) = polar Q x y := by
    rw [QuadraticMap.map_add Q x y, ← hxy]
    linear_combination Q x * h2
  have hpol' : polar Q (x + y) x = polar Q x y := by
    rw [polar_add_left, polar_self_eq_two_mul, h2, zero_mul, zero_add, polar_comm]
  rw [reflect_apply (hQ ▸ hpol), hpol', hQ, div_self hpol, one_smul, sub_add_eq_sub_sub, sub_self,
    zero_sub, neg_eq_self_of_two_eq_zero h2]

theorem exists_singular_polar_ne_zero (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) = 0)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hxy : polar Q x y = 0) : ∃ z, Q z = 0 ∧ polar Q x z ≠ 0 ∧ polar Q z y ≠ 0 := by
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx hx0
  obtain ⟨P', rfl⟩ := exists_hypPair hQ hy hy0
  by_cases h1 : polar Q P.f P'.e = 0
  · by_cases h3 : polar Q P.e P'.f = 0
    · refine ⟨P.f + P'.f + polar Q P.f P'.f • P.e, ?_, ?_, ?_⟩
      · rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, P.Q_f, P'.Q_f, P.Q_e,
          polar_smul_right_eq, polar_add_left, P.polar_fe, polar_comm Q P'.f P.e, h3]
        linear_combination polar Q P.f P'.f * h2
      · rw [polar_add_right, polar_add_right, polar_smul_right_eq, P.polar_ef, h3,
          polar_self_eq_zero P.Q_e]
        simp
      · rw [polar_add_left, polar_add_left, polar_smul_left_eq, h1, P'.polar_fe, hxy]
        simp
    · exact ⟨P'.f, P'.Q_f, h3, by rw [P'.polar_fe]; exact one_ne_zero⟩
  · exact ⟨P.f, P.Q_f, by rw [P.polar_ef]; exact one_ne_zero, h1⟩

theorem exists_mem_orthogonalGroup_apply_eq (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (2 : K) = 0) {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g x = y := by
  by_cases hxy : polar Q x y = 0
  · obtain ⟨z, hz, hxz, hzy⟩ := exists_singular_polar_ne_zero hQ h2 hx hy hx0 hy0 hxy
    refine ⟨reflect Q (z + y) * reflect Q (x + z),
      mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _), ?_⟩
    rw [LinearEquiv.mul_apply, reflect_add_apply h2 (hx.trans hz.symm) hxz,
      reflect_add_apply h2 (hz.trans hy.symm) hzy]
  · exact ⟨reflect Q (x + y), reflect_mem_orthogonalGroup Q _,
      reflect_add_apply h2 (hx.trans hy.symm) hxy⟩

theorem exists_mem_orthogonalGroup_apply_pair (hQ : (polarBilin Q).Nondegenerate)
    (h2 : (2 : K) = 0) (P P' : HypPair Q) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g P.e = P'.e ∧ g P.f = P'.f := by
  obtain ⟨g, hg, hge⟩ :=
    exists_mem_orthogonalGroup_apply_eq hQ h2 P.Q_e P'.Q_e P.e_ne_zero P'.e_ne_zero
  have hQf : Q (g P.f) = Q P'.f := by rw [map_of_mem hg, P.Q_f, P'.Q_f]
  have hpol : polar Q P'.e (g P.f) = 1 := by rw [← hge, polar_map_of_mem hg, P.polar_ef]
  refine ⟨eichler Q P'.e ((1 : K)⁻¹ • (P'.f - g P.f)) * g,
    mul_mem (eichler_mem_orthogonalGroup Q _ _) hg, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hge, eichler_apply_self]
  · rw [LinearEquiv.mul_apply,
      eichler_apply_eq_of_polar_eq P'.Q_e hQf hpol P'.polar_ef one_ne_zero]

end CFSG.Timmesfeld.ClassicalOrders
