module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmField
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData QuadraticMap

namespace OmPlusFourField

open Triality

variable {K : Type} [Field K]

section Roots

@[expose] def rootP : Fin 4 → ℤ := ![1, 2, 1, 1]

@[expose] def rootM : Fin 4 → ℤ := ![-1, 0, 0, 0]

@[expose] def rootZ : Fin 4 → ℤ := ![0, 0, 0, 1]

theorem toStdD_rootP : toStdD 4 rootP = lv 0 1 true true := by decide

theorem toStdD_rootM : toStdD 4 rootM = lv 0 1 false true := by decide

theorem toStdD_rootZ : toStdD 4 rootZ = lv 2 3 true true := by decide

theorem tri_rootP : tri rootP = rootM := by decide

theorem tri_rootM : tri rootM = rootZ := by decide

theorem tri_rootZ : tri rootZ = rootP := by decide

theorem rootP_mem : rootP ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨0, 1, by decide, true, true, toStdD_rootP⟩

theorem rootM_mem : rootM ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨0, 1, by decide, false, true, toStdD_rootM⟩

theorem rootZ_mem : rootZ ∈ rootsD4 :=
  mem_rootsD4_iff.2 ⟨2, 3, by decide, true, true, toStdD_rootZ⟩

end Roots

section Vectors

theorem polar_mulVec_eq_zero {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {A B w : matrixDerived Q}
    (hAB : A = w * B * w⁻¹) {y e t : Fin d → K} {c : K} (hc : c ≠ 0)
    (hB : Matrix.mulVec ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y = y - c • e)
    (hA : ∀ z,
      polar Q (Matrix.mulVec ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) z - z) t = 0) :
    polar Q (Matrix.mulVec ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) e) t = 0 := by
  have hAw : A * w = w * B := by rw [hAB, inv_mul_cancel_right]
  have h1 : Matrix.mulVec ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      (Matrix.mulVec ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y) -
        Matrix.mulVec ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y =
      -(c • Matrix.mulVec ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) e) := by
    rw [← AutOm.mulVec_mul, hAw, AutOm.mulVec_mul, hB, Matrix.mulVec_sub, Matrix.mulVec_smul]
    abel
  have h2 := hA (Matrix.mulVec ((w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y)
  rw [h1, polar_neg_left, polar_smul_left, smul_eq_mul, neg_eq_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_left hc

section CharTwo

variable [CharP K 2]

theorem polar_X8_sub_eq_zero {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) (z x : Fin (2 * 4) → K)
    (hj : polar (coordinateQuadPlus 4 K) (AutOm.pvec j t) x = 0)
    (hi : polar (coordinateQuadPlus 4 K) (AutOm.pvec i s) x = 0) :
    polar (coordinateQuadPlus 4 K)
      (Matrix.mulVec ((X8 γ c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) z -
        z) x = 0 := by
  rw [X8_mulVec hij h c]
  have e : AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec j t) (c • AutOm.pvec i s) z - z =
      polar (coordinateQuadPlus 4 K) z (AutOm.pvec j t) • (c • AutOm.pvec i s) -
        polar (coordinateQuadPlus 4 K) z (c • AutOm.pvec i s) • AutOm.pvec j t -
        (coordinateQuadPlus 4 K (c • AutOm.pvec i s) *
          polar (coordinateQuadPlus 4 K) z (AutOm.pvec j t)) • AutOm.pvec j t := by
    rw [AutOm.eichlerC]
    abel
  rw [e, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_smul_left,
    polar_smul_left, hi, hj]
  simp

theorem X8_rootP_f0 (c : K) :
    Matrix.mulVec ((X8 rootP c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      (AutOm.pvec 0 false) = AutOm.pvec 0 false - c • AutOm.pvec 1 true := by
  rw [X8_mulVec (by decide) toStdD_rootP]
  simp only [AutOm.eichlerC, polar_smul_right, AutOm.polar_pvec, QuadraticMap.map_smul,
    AutOm.form_pvec]
  simp

theorem X8_rootM_e0 (c : K) :
    Matrix.mulVec ((X8 rootM c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      (AutOm.pvec 0 true) = AutOm.pvec 0 true - c • AutOm.pvec 1 true := by
  rw [X8_mulVec (by decide) toStdD_rootM]
  simp only [AutOm.eichlerC, polar_smul_right, AutOm.polar_pvec, QuadraticMap.map_smul,
    AutOm.form_pvec]
  simp

theorem X8_one_ne_one {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) : X8 γ (1 : K) ≠ 1 := by
  obtain ⟨i, j, s, t, hij, h, -⟩ := exists_eq_fromStd hγ
  intro h1
  have e := X8_mulVec hij h (1 : K) (AutOm.pvec i (!s))
  rw [h1] at e
  have e2 := congrArg (fun v => polar (coordinateQuadPlus 4 K) v (AutOm.pvec j (!t))) e
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, AutOm.eichlerC, one_smul,
    AutOm.form_pvec, zero_mul, zero_smul, sub_zero, polar_add_left, polar_sub_left,
    polar_smul_left, AutOm.polar_pvec] at e2
  simp [hij] at e2

end CharTwo

theorem pvec_one_true_ne_zero : (AutOm.pvec (1 : Fin 4) true : Fin (2 * 4) → K) ≠ 0 := by
  intro h
  have h2 := AutOm.polar_pvec_not (K := K) (1 : Fin 4) true
  rw [h, polar_zero_left] at h2
  exact zero_ne_one h2

theorem eq_zero_of_perp (r : Bool) {v : Fin (2 * 4) → K}
    (h1 : ∀ x, polar (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) x = 0 →
      polar (coordinateQuadPlus 4 K) (AutOm.pvec 0 r) x = 0 →
        polar (coordinateQuadPlus 4 K) v x = 0)
    (h2 : ∀ x, polar (coordinateQuadPlus 4 K) (AutOm.pvec 3 true) x = 0 →
      polar (coordinateQuadPlus 4 K) (AutOm.pvec 2 true) x = 0 →
        polar (coordinateQuadPlus 4 K) v x = 0) : v = 0 := by
  refine AutOm.eq_zero_of_polar_pvec fun k b => ?_
  fin_cases k <;> cases b <;> cases r <;>
    first
    | exact h1 _ (by rw [AutOm.polar_pvec]; exact ite_eq_right (by decide))
        (by rw [AutOm.polar_pvec]; exact ite_eq_right (by decide))
    | exact h2 _ (by rw [AutOm.polar_pvec]; exact ite_eq_right (by decide))
        (by rw [AutOm.polar_pvec]; exact ite_eq_right (by decide))

end Vectors

section Main

variable [CharP K 2]

theorem xr_mem_plusRootGroup {δ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 δ = lv i j s t) (c : K) : xr δ c ∈ plusRootGroup 4 K three_le_four δ := by
  rw [plusRootGroup_eq three_le_four hij s t h, xr_eq_longRoot hij h c]
  exact ⟨_, rfl⟩

theorem exists_eq_X8_of_mem {δ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 δ = lv i j s t) {z : Sp8 K} (hz : z ∈ plusRootGroup 4 K three_le_four δ) :
    ∃ c : K, model8 z = X8 δ c := by
  rw [plusRootGroup_eq three_le_four hij s t h] at hz
  obtain ⟨c, rfl⟩ := hz
  exact ⟨Multiplicative.toAdd c, by rw [X8, xr_eq_longRoot hij h]; rfl⟩

omit [CharP K 2] in
theorem X8_zero (δ : Fin 4 → ℤ) : X8 δ (0 : K) = 1 := by
  rw [X8, xr, CFSG.LieType.Steinberg.SpinPlus.x, CFSG.LieType.Steinberg.SpinFrame.rootElt_zero,
    map_one]

theorem exists_conj_X8 {α : MulAut (Om8 K)} {γ g : Om8 K}
    (hg : ∀ δ ∈ (plusDatum 4 K three_le_four).roots,
      ∀ z ∈ (plusDatum 4 K three_le_four).rootGroup δ,
        ∃ z' ∈ (plusDatum 4 K three_le_four).rootGroup δ,
          g⁻¹ * (MulAut.conj γ * α) (AutOm.spinModelPlus three_le_four z) * g =
            AutOm.spinModelPlus three_le_four z')
    {δ δ' : Fin 4 → ℤ} (hδ : δ ∈ rootsD4) (hδ' : δ' ∈ rootsD4) {i j : Fin 4} (hij : i ≠ j)
    {s t : Bool} (h : toStdD 4 δ = lv i j s t) (hα : α (X8 δ 1) = X8 δ' 1) :
    ∃ c : K, c ≠ 0 ∧ X8 δ' 1 = (γ⁻¹ * g) * X8 δ c * (γ⁻¹ * g)⁻¹ := by
  obtain ⟨z', hz', e⟩ := hg δ hδ (xr δ 1) (xr_mem_plusRootGroup hij h 1)
  obtain ⟨c, hc⟩ := exists_eq_X8_of_mem hij h hz'
  have e' : X8 δ' (1 : K) = (γ⁻¹ * g) * X8 δ c * (γ⁻¹ * g)⁻¹ := by
    have e2 : g⁻¹ * (γ * X8 δ' 1 * γ⁻¹) * g = X8 δ c := by
      rw [← hc, ← e, MulAut.mul_apply, MulAut.conj_apply]
      exact congrArg (fun y => g⁻¹ * (γ * y * γ⁻¹) * g) hα.symm
    rw [← e2]
    group
  refine ⟨c, fun hc0 => X8_one_ne_one (K := K) hδ' ?_, e'⟩
  rw [e', hc0, X8_zero, mul_one, mul_inv_cancel]

variable [Finite K]

theorem theta_pow_fieldAutP_X8 {k : ℕ} (σ : K ≃+* K) {δ δ' : Fin 4 → ℤ} (hδ : δ ∈ rootsD4)
    (h : (theta ^ k : MulAut (Om8 K)) (X8 δ 1) = X8 δ' 1) :
    (theta ^ k * AutOm.fieldAutP 4 σ : MulAut (Om8 K)) (X8 δ 1) = X8 δ' 1 := by
  rw [MulAut.mul_apply, fieldAutP_X8 σ hδ, map_one, h]

theorem theta_sq_X8 {δ : Fin 4 → ℤ} (hδ : δ ∈ rootsD4) :
    (theta ^ 2 : MulAut (Om8 K)) (X8 δ 1) = X8 (tri (tri δ)) 1 := by
  rw [pow_two, MulAut.mul_apply, theta_X8 hδ, theta_X8 (tri_mem_roots hδ)]

theorem not_modelDiagField_theta_pow (γ : Om8 K) {k : ℕ} (hk : k = 1 ∨ k = 2) (σ : K ≃+* K) :
    ¬ OrdPGraph.ModelDiagField (plusDatum 4 K three_le_four) (AutOm.spinModelPlus three_le_four)
      (MulAut.conj γ * (theta ^ k * AutOm.fieldAutP 4 σ)) := by
  rintro ⟨g, hg⟩
  set w : Om8 K := γ⁻¹ * g
  suffices hv : Matrix.mulVec ((w : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      (AutOm.pvec 1 true) = 0 by
    apply pvec_one_true_ne_zero (K := K)
    have e := AutOm.mulVec_mul w⁻¹ w (AutOm.pvec 1 true)
    rw [inv_mul_cancel, hv, Matrix.mulVec_zero] at e
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec] at e
    exact e
  rcases hk with rfl | rfl
  ·
    obtain ⟨c₁, hc₁, e₁⟩ := exists_conj_X8 hg rootP_mem rootM_mem (by decide) toStdD_rootP
      (theta_pow_fieldAutP_X8 σ rootP_mem (by rw [pow_one, theta_X8 rootP_mem, tri_rootP]))
    obtain ⟨c₂, hc₂, e₂⟩ := exists_conj_X8 hg rootM_mem rootZ_mem (by decide) toStdD_rootM
      (theta_pow_fieldAutP_X8 σ rootM_mem (by rw [pow_one, theta_X8 rootM_mem, tri_rootM]))
    exact eq_zero_of_perp false
      (fun x hj hi => polar_mulVec_eq_zero e₁ hc₁ (X8_rootP_f0 c₁)
        fun z => polar_X8_sub_eq_zero (by decide) toStdD_rootM 1 z x hj hi)
      (fun x hj hi => polar_mulVec_eq_zero e₂ hc₂ (X8_rootM_e0 c₂)
        fun z => polar_X8_sub_eq_zero (by decide) toStdD_rootZ 1 z x hj hi)
  ·
    obtain ⟨c₁, hc₁, e₁⟩ := exists_conj_X8 hg rootP_mem rootZ_mem (by decide) toStdD_rootP
      (theta_pow_fieldAutP_X8 σ rootP_mem (by rw [theta_sq_X8 rootP_mem, tri_rootP, tri_rootM]))
    obtain ⟨c₂, hc₂, e₂⟩ := exists_conj_X8 hg rootM_mem rootP_mem (by decide) toStdD_rootM
      (theta_pow_fieldAutP_X8 σ rootM_mem (by rw [theta_sq_X8 rootM_mem, tri_rootM, tri_rootZ]))
    exact eq_zero_of_perp true
      (fun x hj hi => polar_mulVec_eq_zero e₂ hc₂ (X8_rootM_e0 c₂)
        fun z => polar_X8_sub_eq_zero (by decide) toStdD_rootP 1 z x hj hi)
      (fun x hj hi => polar_mulVec_eq_zero e₁ hc₁ (X8_rootP_f0 c₁)
        fun z => polar_X8_sub_eq_zero (by decide) toStdD_rootZ 1 z x hj hi)

theorem exists_conj_mul_fieldAutP_of_modelDiagField {β : MulAut (Om8 K)} {e : ℕ}
    (hβ : β ^ 3 ^ e = 1)
    (hMD : OrdPGraph.ModelDiagField (plusDatum 4 K three_le_four)
      (AutOm.spinModelPlus three_le_four) β) :
    ∃ (h : Om8 K) (τ : K ≃+* K), β = MulAut.conj h * AutOm.fieldAutP 4 τ := by
  by_cases hβS : β ∈ inner (Om8 K) ⊔ (AutOm.fieldAutP 4).range
  · obtain ⟨_, ⟨h, rfl⟩, _, ⟨τ, rfl⟩, hβ'⟩ := Subgroup.mem_sup_of_normal_left.1 hβS
    exact ⟨h, τ, hβ'.symm⟩
  · obtain ⟨γ, k, σ, hk, rfl⟩ := L45RankX.exists_conj_theta_pow_fieldAutP_of_pow hβ hβS
    exact absurd hMD (not_modelDiagField_theta_pow γ hk σ)

end Main

end OmPlusFourField

theorem ggOmegaPlusFourDiagFieldInput_holds : GGOmegaPlusFourDiagFieldInput :=
  fun _ _ _ _ _ hβ3 hMD =>
    OmPlusFourField.exists_conj_mul_fieldAutP_of_modelDiagField (e := 1) (by rwa [pow_one]) hMD

section Family

theorem ggOrdPFieldConjPOmegaPlusRest_holds : GGOrdPFieldConjPOmegaPlusRest :=
  ggOrdPFieldConjPOmegaPlusRest_of_fourDiagField ggOmegaPlusFourDiagFieldInput_holds

theorem ggOrdPFieldConjAt_POmegaPlus : GGOrdPFieldConjAt .POmegaPlus :=
  ggOrdPFieldConjAt_POmegaPlus_of_fourDiagField ggOmegaPlusFourDiagFieldInput_holds

end Family

end CFSG.StandardType
