module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankOmega

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.SpinFrame QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Coord

noncomputable abbrev act (x : Om8 K) (y : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  ((x : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y

theorem act_mul (x z : Om8 K) (y : Fin (2 * 4) → K) : act (x * z) y = act x (act z y) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (y : Fin (2 * 4) → K) : act (1 : Om8 K) y = y := by
  simp only [act, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem eq_of_polar_pvec {y z : Fin (2 * 4) → K}
    (h : ∀ k r, polar (coordinateQuadPlus 4 K) y (AutOm.pvec k r) =
      polar (coordinateQuadPlus 4 K) z (AutOm.pvec k r)) : y = z := by
  rw [← sub_eq_zero]
  exact AutOm.eq_zero_of_polar_pvec fun k r => by rw [polar_sub_left, h, sub_self]

theorem mem_ker_iff_act {x : Om8 K} {y : Fin (2 * 4) → K} :
    y ∈ LinearMap.ker (omRep x - 1) ↔ act x y = y :=
  mem_ker_omRep_sub_one

variable [CharP K 2]

theorem polar_act_X8 {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (y : Fin (2 * 4) → K) (l : Fin 4) (u : Bool) :
    polar (coordinateQuadPlus 4 K) (act (X8 γ 1) y) (AutOm.pvec l u) =
      polar (coordinateQuadPlus 4 K) y (AutOm.pvec l u) +
        polar (coordinateQuadPlus 4 K) y (AutOm.pvec j t) * (if i = l ∧ s = !u then 1 else 0) -
        polar (coordinateQuadPlus 4 K) y (AutOm.pvec i s) * (if j = l ∧ t = !u then 1 else 0) := by
  rw [act, X8_mulVec hij h, AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul,
    sub_zero, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, AutOm.polar_pvec,
    AutOm.polar_pvec, smul_eq_mul, smul_eq_mul]

end Coord

abbrev rA : Fin 4 → ℤ := fromStd (lv 0 1 true false)
abbrev rAm : Fin 4 → ℤ := fromStd (lv 0 1 false true)
abbrev rB : Fin 4 → ℤ := fromStd (lv 0 1 true true)
abbrev rBm : Fin 4 → ℤ := fromStd (lv 0 1 false false)

theorem toStdD_rA : toStdD 4 rA = lv 0 1 true false := by decide
theorem toStdD_rAm : toStdD 4 rAm = lv 0 1 false true := by decide
theorem toStdD_rB : toStdD 4 rB = lv 0 1 true true := by decide
theorem toStdD_rBm : toStdD 4 rBm = lv 0 1 false false := by decide
theorem toStdD_tri_rA : toStdD 4 (tri rA) = lv 2 3 false false := by decide
theorem toStdD_tri_rAm : toStdD 4 (tri rAm) = lv 2 3 true true := by decide
theorem toStdD_tri_rB : toStdD 4 (tri rB) = lv 0 1 false true := by decide
theorem toStdD_tri_rBm : toStdD 4 (tri rBm) = lv 0 1 true false := by decide

theorem mem_rootsD4_of_toStdD {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) : γ ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨i, j, hij, s, t, h⟩

section Rep

variable [CharP K 2]

noncomputable abbrev x0 : Om8 K := X8 rA 1 * X8 rAm 1 * X8 rB 1 * X8 rBm 1

noncomputable abbrev cd (y : Fin (2 * 4) → K) (k : Fin 4) (r : Bool) : K :=
  polar (coordinateQuadPlus 4 K) y (AutOm.pvec k r)

theorem idx01 : (0 : Fin 4) ≠ 1 := by decide
theorem idx23 : (2 : Fin 4) ≠ 3 := by decide

theorem x0_cd0f (y : Fin (2 * 4) → K) : cd (act (x0 (K := K)) y) 0 false = cd y 0 true := by
  simp only [cd, x0, act_mul, polar_act_X8 idx01 toStdD_rA, polar_act_X8 idx01 toStdD_rAm,
    polar_act_X8 idx01 toStdD_rB, polar_act_X8 idx01 toStdD_rBm]
  simp
  simp only [CharTwo.neg_eq]

theorem x0_cd1f (y : Fin (2 * 4) → K) :
    cd (act (x0 (K := K)) y) 1 false = cd y 0 true + cd y 1 true := by
  simp only [cd, x0, act_mul, polar_act_X8 idx01 toStdD_rA, polar_act_X8 idx01 toStdD_rAm,
    polar_act_X8 idx01 toStdD_rB, polar_act_X8 idx01 toStdD_rBm]
  simp
  simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]

theorem x0_cd0t (y : Fin (2 * 4) → K) :
    cd (act (x0 (K := K)) y) 0 true = cd y 0 false + cd y 1 false + cd y 0 true + cd y 1 true := by
  simp only [cd, x0, act_mul, polar_act_X8 idx01 toStdD_rA, polar_act_X8 idx01 toStdD_rAm,
    polar_act_X8 idx01 toStdD_rB, polar_act_X8 idx01 toStdD_rBm]
  simp
  simp only [CharTwo.sub_eq_add]
  ring

theorem x0_cd1t (y : Fin (2 * 4) → K) :
    cd (act (x0 (K := K)) y) 1 true = cd y 1 false + cd y 0 true := by
  simp only [cd, x0, act_mul, polar_act_X8 idx01 toStdD_rA, polar_act_X8 idx01 toStdD_rAm,
    polar_act_X8 idx01 toStdD_rB, polar_act_X8 idx01 toStdD_rBm]
  simp
  simp only [CharTwo.neg_eq]

theorem x0_cd_other (y : Fin (2 * 4) → K) {l : Fin 4} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (u : Bool) :
    cd (act (x0 (K := K)) y) l u = cd y l u := by
  simp only [cd, x0, act_mul, polar_act_X8 idx01 toStdD_rA, polar_act_X8 idx01 toStdD_rAm,
    polar_act_X8 idx01 toStdD_rB, polar_act_X8 idx01 toStdD_rBm]
  simp [hl0.symm, hl1.symm]

theorem x0_pow_three : (x0 (K := K)) ^ 3 = 1 := by
  have h3 : ∀ y, act ((x0 (K := K)) ^ 3) y = y := by
    intro y
    rw [pow_succ, pow_succ, pow_one, act_mul, act_mul]
    refine eq_of_polar_pvec fun l u => ?_
    change cd _ l u = cd y l u
    by_cases hl0 : l = 0
    · subst hl0
      cases u
      · simp only [x0_cd0f, x0_cd1f, x0_cd0t, x0_cd1t]; grind
      · simp only [x0_cd0f, x0_cd1f, x0_cd0t, x0_cd1t]; grind
    · by_cases hl1 : l = 1
      · subst hl1
        cases u
        · simp only [x0_cd0f, x0_cd1f, x0_cd0t, x0_cd1t]; grind
        · simp only [x0_cd0f, x0_cd1f, x0_cd0t, x0_cd1t]; grind
      · rw [x0_cd_other _ hl0 hl1, x0_cd_other _ hl0 hl1, x0_cd_other _ hl0 hl1]
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact (h3 y).trans (by rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec])

omit [CharP K 2] in
theorem cd_pvec (y : Fin 4) (r : Bool) (k : Fin 4) (u : Bool) :
    cd (AutOm.pvec y r : Fin (2 * 4) → K) k u = if y = k ∧ r = !u then 1 else 0 :=
  AutOm.polar_pvec y k r u

theorem x0_ne_one : (x0 (K := K)) ≠ 1 := by
  intro h
  have e := x0_cd0f (K := K) (AutOm.pvec 0 false)
  rw [h, act_one, cd_pvec, cd_pvec] at e
  simp at e

theorem act_x0_of {y : Fin (2 * 4) → K} (h1 : cd y 0 true + cd y 0 false = 0)
    (h2 : cd y 1 true + cd y 0 false + cd y 1 false = 0) : act (x0 (K := K)) y = y := by
  refine eq_of_polar_pvec fun l u => ?_
  change cd _ l u = cd y l u
  by_cases hl0 : l = 0
  · subst hl0
    cases u
    · rw [x0_cd0f]; grind
    · rw [x0_cd0t]; grind
  · by_cases hl1 : l = 1
    · subst hl1
      cases u
      · rw [x0_cd1f]; grind
      · rw [x0_cd1t]; grind
    · exact x0_cd_other y hl0 hl1 u

theorem x0_fix_e2f2 :
    act (x0 (K := K)) (AutOm.pvec 2 true + AutOm.pvec 2 false) =
      AutOm.pvec 2 true + AutOm.pvec 2 false := by
  have hc : ∀ k : Fin 4, k ≠ 2 → ∀ u, cd (AutOm.pvec 2 true + AutOm.pvec 2 false : Fin (2 * 4) → K)
      k u = 0 := by
    intro k hk u
    rw [cd, polar_add_left, AutOm.polar_pvec_of_ne (Ne.symm hk),
      AutOm.polar_pvec_of_ne (Ne.symm hk), add_zero]
  refine act_x0_of ?_ ?_
  · rw [hc 0 (by decide), hc 0 (by decide), add_zero]
  · rw [hc 1 (by decide), hc 0 (by decide), hc 1 (by decide), add_zero, add_zero]

theorem omFixDim_x0 : omFixDim (x0 (K := K)) = 6 := by
  set Q := coordinateQuadPlus 4 K
  set l₁ : (Fin (2 * 4) → K) →ₗ[K] K :=
    (QuadraticMap.polarBilin Q).flip (AutOm.pvec 0 true + AutOm.pvec 0 false)
  set l₂ : (Fin (2 * 4) → K) →ₗ[K] K :=
    (QuadraticMap.polarBilin Q).flip (AutOm.pvec 1 true + AutOm.pvec 0 false + AutOm.pvec 1 false)
  have hle : LinearMap.ker (l₁.prod l₂) ≤ LinearMap.ker (omRep (x0 (K := K)) - 1) := by
    intro y hy
    have hy0 := LinearMap.mem_ker.mp hy
    have hy1 : polar Q y (AutOm.pvec 0 true + AutOm.pvec 0 false) = 0 := congrArg Prod.fst hy0
    have hy2 : polar Q y (AutOm.pvec 1 true + AutOm.pvec 0 false + AutOm.pvec 1 false) = 0 :=
      congrArg Prod.snd hy0
    rw [polar_add_right] at hy1
    rw [polar_add_right, polar_add_right] at hy2
    rw [mem_ker_iff_act]
    exact act_x0_of hy1 hy2
  have hrn := LinearMap.finrank_range_add_finrank_ker (l₁.prod l₂)
  have hr : finrank K (LinearMap.range (l₁.prod l₂)) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (l₁.prod l₂))
    rwa [Module.finrank_prod, Module.finrank_self] at this
  rw [Module.finrank_fin_fun] at hrn
  have hge : 6 ≤ omFixDim (x0 (K := K)) := by
    have h1 : finrank K (LinearMap.ker (l₁.prod l₂)) ≤ omFixDim (x0 (K := K)) :=
      Submodule.finrank_mono hle
    omega
  have hle8 : omFixDim (x0 (K := K)) ≤ 8 := by
    have := Submodule.finrank_le (LinearMap.ker (omRep (x0 (K := K)) - 1))
    rwa [Module.finrank_fin_fun] at this
  have h8 : omFixDim (x0 (K := K)) ≠ 8 := fun h => x0_ne_one (eq_one_of_omFixDim h)
  obtain ⟨j, hj⟩ := omFixDim_even (x0 (K := K)) x0_pow_three
  omega

end Rep

section Theta

variable [CharP K 2] [Finite K]

theorem theta_x0 : theta (x0 (K := K)) =
    X8 (tri rA) 1 * X8 (tri rAm) 1 * X8 (tri rB) 1 * X8 (tri rBm) 1 := by
  simp only [x0, map_mul, theta_X8 (mem_rootsD4_of_toStdD idx01 toStdD_rA),
    theta_X8 (mem_rootsD4_of_toStdD idx01 toStdD_rAm),
    theta_X8 (mem_rootsD4_of_toStdD idx01 toStdD_rB),
    theta_X8 (mem_rootsD4_of_toStdD idx01 toStdD_rBm)]

theorem eq_zero_of_act_theta_x0 {y : Fin (2 * 4) → K} (h : act (theta (x0 (K := K))) y = y) :
    y = 0 := by
  have e : ∀ l u, cd (act (theta (x0 (K := K))) y) l u = cd y l u := fun l u => by rw [h]
  rw [theta_x0] at e
  simp only [cd, act_mul, polar_act_X8 idx23 toStdD_tri_rA, polar_act_X8 idx23 toStdD_tri_rAm,
    polar_act_X8 idx01 toStdD_tri_rB, polar_act_X8 idx01 toStdD_tri_rBm] at e
  have e0f := e 0 false
  have e0t := e 0 true
  have e1f := e 1 false
  have e1t := e 1 true
  have e2f := e 2 false
  have e2t := e 2 true
  have e3f := e 3 false
  have e3t := e 3 true
  simp at e0f e0t e1f e1t e2f e2t e3f e3t
  refine AutOm.eq_zero_of_polar_pvec fun k r => ?_
  fin_cases k <;> cases r <;> simp <;> grind

theorem omFixDim_theta_x0 : omFixDim (theta (x0 (K := K))) = 0 := by
  rw [omFixDim, fixDim, Submodule.finrank_eq_zero, eq_bot_iff]
  intro y hy
  rw [Submodule.mem_bot]
  exact eq_zero_of_act_theta_x0 (mem_ker_iff_act.mp hy)

end Theta


end D4Rank

end CFSG.StandardType
