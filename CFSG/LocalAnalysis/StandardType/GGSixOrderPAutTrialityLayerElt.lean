module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClassRep
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEightLin

public section

namespace CFSG.StandardType

namespace OrdPTriLayer

open Module CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.SpinFrame QuadraticMap

variable {K : Type} [Field K]

@[expose] def rootB : Fin 4 → ℤ := ![0, 0, 1, 0]

theorem toStdD_rootB : toStdD 4 rootB = lv 2 3 true false := by decide

theorem tri_rootB : tri rootB = rootB := by decide

theorem tri_rootA : tri rootA = rootC := by decide

theorem rootB_mem : rootB ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨2, 3, by decide, true, false, toStdD_rootB⟩

theorem idx12 : (1 : Fin 4) ≠ 2 := by decide

theorem idx03 : (0 : Fin 4) ≠ 3 := by decide

theorem eq_of_act {x z : Om8 K} (h : ∀ y, act x y = act z y) : x = z := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact h y

section CharTwo

variable [CharP K 2]

noncomputable abbrev ureg : Om8 K := X8 rootB 1 * X8 rootA 1 * X8 rootC 1 * X8 rootD 1

theorem ureg_cd0f (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 0 false = cd y 0 false + cd y 3 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp

theorem ureg_cd1f (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 1 false = cd y 1 false + cd y 2 false := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp

theorem ureg_cd2f (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 2 false =
      cd y 2 false + cd y 3 false + cd y 0 true + cd y 0 false + cd y 3 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp
  simp only [CharTwo.sub_eq_add]
  ring

theorem ureg_cd3f (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 3 false =
      cd y 3 false + cd y 0 true + cd y 0 false + cd y 3 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp
  simp only [CharTwo.sub_eq_add]
  ring

theorem ureg_cd0t (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 0 true = cd y 0 true + cd y 3 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp

theorem ureg_cd1t (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 1 true = cd y 1 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp

theorem ureg_cd2t (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 2 true = cd y 2 true + cd y 1 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp
  simp only [CharTwo.sub_eq_add]

theorem ureg_cd3t (y : Fin (2 * 4) → K) :
    cd (act (ureg (K := K)) y) 3 true = cd y 3 true + cd y 2 true + cd y 1 true := by
  simp only [cd, ureg, act_mul, polar_act_X8 idx23 toStdD_rootB, polar_act_X8 idx12 toStdD_rootA,
    polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx03 toStdD_rootD]
  simp
  simp only [CharTwo.sub_eq_add]
  ring

noncomputable abbrev nreg : Module.End K (Fin (2 * 4) → K) := omRep (ureg (K := K)) - 1

omit [CharP K 2] in
theorem cd_nreg (y : Fin (2 * 4) → K) (k : Fin 4) (r : Bool) :
    cd (nreg y) k r = cd (act (ureg (K := K)) y) k r - cd y k r := by
  rw [LinearMap.sub_apply, Module.End.one_apply, omRep_apply, cd, cd, cd, polar_sub_left]

theorem nreg_cd0f (y : Fin (2 * 4) → K) : cd (nreg y) 0 false = cd y 3 true := by
  rw [cd_nreg, ureg_cd0f]; ring

theorem nreg_cd1f (y : Fin (2 * 4) → K) : cd (nreg y) 1 false = cd y 2 false := by
  rw [cd_nreg, ureg_cd1f]; ring

theorem nreg_cd2f (y : Fin (2 * 4) → K) :
    cd (nreg y) 2 false = cd y 3 false + cd y 0 true + cd y 0 false + cd y 3 true := by
  rw [cd_nreg, ureg_cd2f]; ring

theorem nreg_cd3f (y : Fin (2 * 4) → K) :
    cd (nreg y) 3 false = cd y 0 true + cd y 0 false + cd y 3 true := by
  rw [cd_nreg, ureg_cd3f]; ring

theorem nreg_cd0t (y : Fin (2 * 4) → K) : cd (nreg y) 0 true = cd y 3 true := by
  rw [cd_nreg, ureg_cd0t]; ring

theorem nreg_cd1t (y : Fin (2 * 4) → K) : cd (nreg y) 1 true = 0 := by
  rw [cd_nreg, ureg_cd1t]; ring

theorem nreg_cd2t (y : Fin (2 * 4) → K) : cd (nreg y) 2 true = cd y 1 true := by
  rw [cd_nreg, ureg_cd2t]; ring

theorem nreg_cd3t (y : Fin (2 * 4) → K) : cd (nreg y) 3 true = cd y 2 true + cd y 1 true := by
  rw [cd_nreg, ureg_cd3t]; ring

@[expose] def InFlag (i : ℕ) (y : Fin (2 * 4) → K) : Prop :=
  (i < 1 → cd y 1 false = 0) ∧ (i < 2 → cd y 2 false = 0) ∧ (i < 3 → cd y 3 false = 0) ∧
    (i < 4 → cd y 0 false = 0) ∧ (i < 5 → cd y 0 true = 0) ∧ (i < 6 → cd y 3 true = 0) ∧
      (i < 7 → cd y 2 true = 0) ∧ (i < 8 → cd y 1 true = 0)

omit [CharP K 2] in
theorem inFlag_eight (y : Fin (2 * 4) → K) : InFlag 8 y :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

omit [CharP K 2] in
theorem eq_zero_of_inFlag_zero {y : Fin (2 * 4) → K} (h : InFlag 0 y) : y = 0 := by
  obtain ⟨h1f, h2f, h3f, h0f, h0t, h3t, h2t, h1t⟩ := h
  refine AutOm.eq_zero_of_polar_pvec fun k r => ?_
  fin_cases k <;> cases r
  · exact h0f (by omega)
  · exact h0t (by omega)
  · exact h1f (by omega)
  · exact h1t (by omega)
  · exact h2f (by omega)
  · exact h2t (by omega)
  · exact h3f (by omega)
  · exact h3t (by omega)

theorem nreg_flag {i : ℕ} {y : Fin (2 * 4) → K} (h : InFlag (i + 1) y) : InFlag i (nreg y) := by
  obtain ⟨h1f, h2f, h3f, h0f, h0t, h3t, h2t, h1t⟩ := h
  refine ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_, fun hi => ?_, fun hi => ?_, fun hi => ?_,
    fun hi => ?_, fun hi => ?_⟩
  · rw [nreg_cd1f, h2f (by omega)]
  · rw [nreg_cd2f, h3f (by omega), h0t (by omega), h0f (by omega), h3t (by omega)]; ring
  · rw [nreg_cd3f, h0t (by omega), h0f (by omega), h3t (by omega)]; ring
  · rw [nreg_cd0f, h3t (by omega)]
  · rw [nreg_cd0t, h3t (by omega)]
  · rw [nreg_cd3t, h2t (by omega), h1t (by omega)]; ring
  · rw [nreg_cd2t, h1t (by omega)]
  · rw [nreg_cd1t]

theorem nreg_pow_flag (j : ℕ) : ∀ (i : ℕ) (y : Fin (2 * 4) → K), InFlag (i + j) y →
    InFlag i ((nreg ^ j) y) := by
  induction j with
  | zero => intro i y h; simpa using h
  | succ j ih =>
    intro i y h
    rw [pow_succ, Module.End.mul_apply]
    exact ih i _ (nreg_flag (by rwa [← add_assoc] at h))

theorem nreg_pow_eight : (nreg (K := K)) ^ 8 = 0 :=
  LinearMap.ext fun y => eq_zero_of_inFlag_zero (nreg_pow_flag 8 0 y (by
    rw [zero_add]; exact inFlag_eight y))

theorem ureg_pow_eight : (ureg (K := K)) ^ 8 = 1 := by
  refine eq_one_of_omFixDim ?_
  show finrank K (LinearMap.ker (omRep ((ureg (K := K)) ^ 8) - 1)) = 8
  rw [map_pow, ← OrdPTriEight.sub_one_pow_eight, nreg_pow_eight, LinearMap.ker_zero, finrank_top,
    Module.finrank_fin_fun]

theorem cd_nreg_pow_four :
    cd ((nreg ^ 4) (AutOm.pvec 2 false : Fin (2 * 4) → K)) 1 false = 1 := by
  rw [pow_succ, pow_succ, pow_succ, pow_one]
  simp only [Module.End.mul_apply, nreg_cd0f, nreg_cd1f, nreg_cd2f, nreg_cd3f, nreg_cd0t, nreg_cd1t,
    nreg_cd2t, nreg_cd3t, cd_pvec]
  simp [CharTwo.add_self_eq_zero]

theorem ureg_pow_four_ne_one : (ureg (K := K)) ^ 4 ≠ 1 := by
  intro h
  have h4 : (nreg (K := K)) ^ 4 = 0 := by
    rw [OrdPTriEight.sub_one_pow_four, ← map_pow, h, map_one, sub_self]
  have e := cd_nreg_pow_four (K := K)
  rw [h4, LinearMap.zero_apply, cd, polar_zero_left] at e
  exact zero_ne_one e

theorem orderOf_ureg : orderOf (ureg (K := K)) = 8 := by
  have h4 : ¬ (ureg (K := K)) ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact ureg_pow_four_ne_one
  have h8 : (ureg (K := K)) ^ 2 ^ (2 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]; exact ureg_pow_eight
  rw [orderOf_eq_prime_pow h4 h8]
  norm_num

theorem commute_rootC_rootA : X8 rootC (1 : K) * X8 rootA 1 = X8 rootA 1 * X8 rootC 1 := by
  refine eq_of_act fun y => eq_of_polar_pvec fun l u => ?_
  simp only [act_mul, polar_act_X8 idx03 toStdD_rootC, polar_act_X8 idx12 toStdD_rootA]
  fin_cases l <;> cases u <;> simp

theorem commute_rootD_rootA : X8 rootD (1 : K) * X8 rootA 1 = X8 rootA 1 * X8 rootD 1 := by
  refine eq_of_act fun y => eq_of_polar_pvec fun l u => ?_
  simp only [act_mul, polar_act_X8 idx03 toStdD_rootD, polar_act_X8 idx12 toStdD_rootA]
  fin_cases l <;> cases u <;> simp

theorem theta_ureg [Finite K] : theta (ureg (K := K)) = ureg := by
  simp only [ureg, map_mul, theta_X8 rootB_mem, theta_X8 rootA_mem, theta_X8 rootC_mem,
    theta_X8 rootD_mem, tri_rootB, tri_rootA, tri_rootC, tri_rootD]
  rw [mul_assoc (X8 rootB 1 * X8 rootC 1), commute_rootD_rootA, ← mul_assoc,
    mul_assoc (X8 rootB 1), commute_rootC_rootA, ← mul_assoc]

theorem fieldAutP_ureg [Finite K] (σ : K ≃+* K) : AutOm.fieldAutP 4 σ (ureg (K := K)) = ureg := by
  simp only [ureg, map_mul, fieldAutP_X8 σ rootB_mem, fieldAutP_X8 σ rootA_mem,
    fieldAutP_X8 σ rootC_mem, fieldAutP_X8 σ rootD_mem, map_one]

end CharTwo

end OrdPTriLayer

end CFSG.StandardType
