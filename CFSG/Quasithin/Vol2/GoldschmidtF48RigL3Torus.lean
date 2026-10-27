module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45PgBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus

public section

namespace CFSG.Quasithin.H13.F431.F48L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3 CFSG.Quasithin.H13.F431.F45.PgGeom

variable {F : Type} [Field F]

@[expose] def cartanElt (ω : Fˣ) : projectiveSL 3 F := proj 3 F (dMat ω 1)

theorem dMat_mulVec_apply (t₁ t₂ : Fˣ) (v : V3 F) (i : Fin 3) :
    ((dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i =
      ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)] i * v i := by
  rw [coe_dMat, mulVec_diagonal]

theorem dMat_mulVec_ev (t₁ t₂ : Fˣ) (i : Fin 3) :
    (dMat t₁ t₂ : Matrix (Fin 3) (Fin 3) F) *ᵥ (ev i : V3 F) =
      ![(t₁ : F), (t₂ : F), (((t₁ * t₂)⁻¹ : Fˣ) : F)] i • (ev i : V3 F) := by
  ext j
  rw [dMat_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h
    simp [ev_apply]
  · simp [ev_apply, h]

theorem smul_epts (t₁ t₂ : Fˣ) (i : Fin 3) :
    proj 3 F (dMat t₁ t₂) • (epts i : Pt F) = epts i := by
  refine proj_smul_eq_of_forall _ _ _ fun v hv => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [Matrix.mulVec_smul, dMat_mulVec_ev]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (mem_mkPt (ev_ne_zero i)))

theorem smul_eline (t₁ t₂ : Fˣ) {i j : Fin 3} (h : i ≠ j) :
    proj 3 F (dMat t₁ t₂) • (eline i j h : Ln F) = eline i j h := by
  refine proj_smul_eq_of_gens _ _ _ (v₁ := ev i) (v₂ := ev j) rfl ?_ ?_
  · rw [dMat_mulVec_ev]
    exact Submodule.smul_mem _ _ (ev_mem_eline_left h)
  · rw [dMat_mulVec_ev]
    exact Submodule.smul_mem _ _ (ev_mem_eline_right h)

theorem smul_p0 (t₁ t₂ : Fˣ) : proj 3 F (dMat t₁ t₂) • (p0 : Pt F) = p0 := by
  rw [p0_eq_epts]
  exact smul_epts t₁ t₂ 0

theorem smul_l0 (t₁ t₂ : Fˣ) : proj 3 F (dMat t₁ t₂) • (l0 : Ln F) = l0 := by
  refine proj_smul_eq_of_forall _ _ _ fun v hv => ?_
  rw [mem_l0] at hv ⊢
  rw [dMat_mulVec_apply, hv, mul_zero]

section Centralizer

variable [CharP F 2]

theorem cartanElt_cent {ω : Fˣ} (hω : ω ≠ 1) {x : projectiveSL 3 F}
    (hx : x ∈ projUnitriangular 3 F) (hc : cartanElt ω * x * (cartanElt ω)⁻¹ = x) : x = 1 := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hx
  have hω2 : (ω : F) ^ 2 ≠ 1 := unit_ne_one_sq hω
  have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  unfold cartanElt at hc
  rw [dP_conj_nf] at hc
  obtain ⟨hc1, ha1, hb1⟩ := U_ext hc
  simp only [Units.val_one, inv_one, mul_one] at hc1 ha1 hb1
  have hc0 : c = 0 := by
    have : ((ω : F) ^ 2 - 1) * c = 0 := by linear_combination hc1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω2)
  have ha0 : a = 0 := by
    have : ((ω : F) - 1) * a = 0 := by linear_combination ha1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have hb0 : b = 0 := by
    have : ((ω : F) - 1) * b = 0 := by linear_combination hb1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  rw [hc0, ha0, hb0, wP_zero, xP_zero, yP_zero]
  group

theorem exists_cartan_pt [Finite F] (hq : 2 < Nat.card F) :
    ∃ (h : projectiveSL 3 F) (L₁ L₂ L : Ln F), inc (p0 : Pt F) L₁ ∧ inc (p0 : Pt F) L₂ ∧
      L₁ ≠ L₂ ∧ ¬ inc (p0 : Pt F) L ∧ h • (p0 : Pt F) = p0 ∧ h • L₁ = L₁ ∧ h • L₂ = L₂ ∧
      h • L = L ∧ ∀ q ∈ (V1 : Subgroup (projectiveSL 3 F)), h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨ω, hω⟩ := exists_unit_ne_one hq
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  have d02 : (0 : Fin 3) ≠ 2 := by decide
  have d12 : (1 : Fin 3) ≠ 2 := by decide
  refine ⟨cartanElt ω, l0, eline 0 2 d02, eline 1 2 d12, inc_p0_l0,
    inc_p0_iff.mpr (ev_mem_eline_left d02), ?_, ?_, smul_p0 ω 1, smul_l0 ω 1,
    smul_eline ω 1 d02, smul_eline ω 1 d12, fun q hq hc => cartanElt_cent hω (V1_le_U hq) hc⟩
  · intro h
    have h2 : (ev 2 : V3 F) ∈ (l0 : Ln F).1 := by
      rw [h]
      exact ev_mem_eline_right d02
    have := (mem_l0 _).mp h2
    simp [ev_apply] at this
  · intro h
    have h0 := eline_apply_third d12 d01 d02 (inc_p0_iff.mp h)
    simp [ev_apply] at h0

theorem exists_cartan_ln [Finite F] (hq : 2 < Nat.card F) :
    ∃ (h : projectiveSL 3 F) (P₁ P₂ P : Pt F), inc P₁ (l0 : Ln F) ∧ inc P₂ (l0 : Ln F) ∧
      P₁ ≠ P₂ ∧ ¬ inc P (l0 : Ln F) ∧ h • (l0 : Ln F) = l0 ∧ h • P₁ = P₁ ∧ h • P₂ = P₂ ∧
      h • P = P ∧ ∀ q ∈ (V2 : Subgroup (projectiveSL 3 F)), h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨ω, hω⟩ := exists_unit_ne_one hq
  have d01 : (0 : Fin 3) ≠ 1 := by decide
  refine ⟨cartanElt ω, epts 0, epts 1, epts 2, ?_, ?_, epts_ne d01, ?_, smul_l0 ω 1,
    smul_epts ω 1 0, smul_epts ω 1 1, smul_epts ω 1 2,
    fun q hq hc => cartanElt_cent hω (V2_le_U hq) hc⟩
  · rw [← p0_eq_epts]
    exact inc_p0_l0
  · exact inc_mkPt_iff.mpr ((mem_l0 _).mpr (by simp [ev_apply]))
  · intro h
    have := (mem_l0 _).mp (inc_mkPt_iff.mp h)
    simp [ev_apply] at this

end Centralizer

end CFSG.Quasithin.H13.F431.F48L3
