module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4MS
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountTools

public section

namespace CFSG.Quasithin.H13.Sec1214

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq)
open CFSG.Quasithin.H13.L3321 (SL4)
open CFSG.Quasithin.H13.Case4Count (mem_liftPre_iff)
open scoped Pointwise

theorem mulVec_e0_iff (A : SL4) :
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ↔
      A ∈ FLc.QI 4 {1} := by
  rw [FLc.QI, LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff, Matrix.mulVec_single_one]
  constructor
  · intro h i j hi hj
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    have := congrFun h i
    simp only [Matrix.col_apply] at this
    rw [this, Pi.single_eq_of_ne (fun e => by subst e; simp at hi)]
  · intro h
    have hcol : ∀ i : Fin 4, i ≠ 0 → A.1 i 0 = 0 := fun i hi =>
      h i 0 (by have := Fin.pos_iff_ne_zero.mpr hi; omega) (by simp)
    have h00 : A.1 0 0 = 1 := by
      by_contra h0
      have hz : A.1 0 0 = 0 := by
        generalize A.1 0 0 = x at h0
        revert x
        decide
      have hdet : A.1.det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero 0
        intro i
        by_cases hi : i = 0
        · rw [hi, hz]
        · exact hcol i hi
      rw [A.2] at hdet
      exact one_ne_zero hdet
    funext i
    simp only [Matrix.col_apply]
    by_cases hi : i = 0
    · subst hi
      rw [h00, Pi.single_eq_same]
    · rw [hcol i hi, Pi.single_eq_of_ne hi]

theorem transpose_mulVec_e3_iff (A : SL4) :
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ Pi.single 3 1 = Pi.single 3 1 ↔
      A ∈ FLc.QI 4 {3} := by
  rw [FLc.QI, LocalAnalysis.ComponentInitial.LinearFlag.mem_flagStabilizer]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff, Matrix.mulVec_single_one]
  constructor
  · intro h i j hi hj
    have hi3 : i = 3 := Fin.ext (by have := i.isLt; omega)
    subst hi3
    have := congrFun h j
    simp only [Matrix.col_apply, Matrix.transpose_apply] at this
    rw [this, Pi.single_eq_of_ne (fun e => by subst e; simp at hj)]
  · intro h
    have hrow : ∀ j : Fin 4, j ≠ 3 → A.1 3 j = 0 := fun j hj =>
      h 3 j (by simp) (by have := j.isLt; have : (j : ℕ) ≠ 3 := fun e => hj (Fin.ext e); omega)
    have h33 : A.1 3 3 = 1 := by
      by_contra h0
      have hz : A.1 3 3 = 0 := by
        generalize A.1 3 3 = x at h0
        revert x
        decide
      have hdet : A.1.det = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero 3
        intro j
        by_cases hj : j = 3
        · rw [hj, hz]
        · exact hrow j hj
      rw [A.2] at hdet
      exact one_ne_zero hdet
    funext j
    simp only [Matrix.col_apply, Matrix.transpose_apply]
    by_cases hj : j = 3
    · subst hj
      rw [h33, Pi.single_eq_same]
    · rw [hrow j hj, Pi.single_eq_of_ne hj]

theorem exists_adapted {x₀ f : Fin 4 → ZMod 2} (hx₀ : x₀ ≠ 0) (hf : f ≠ 0) (hxf : x₀ ⬝ᵥ f = 0) :
    ∃ m : SL4, (m : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = x₀ ∧
      (m : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f = Pi.single 3 1 := by
  have he0 : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := fun h => by
    have := congrFun h 0
    simp at this
  obtain ⟨s, hs⟩ := Sec121Q.exists_sl_mulVec_eq he0 hx₀
  set f' := (s : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f with hf'
  have hf'0 : f' 0 = 0 := by
    have hx : ∀ j, x₀ j = (s : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 0 := fun j => by
      rw [← hs, Matrix.mulVec_single_one]
      rfl
    rw [hf', ← hxf]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hx]
  have hf'ne : f' ≠ 0 := by
    intro h0
    apply hf
    have h1 : ((s⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f' = f := by
      rw [hf', Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.one_mulVec]
    rw [← h1, h0, Matrix.mulVec_zero]
  have he3 : (Pi.single 3 1 : Fin 4 → ZMod 2) ≠ 0 := fun h => by
    have := congrFun h 3
    simp at this
  obtain ⟨g, hg, hgf⟩ := VecStab.exists_dual (k := 0) hf'ne he3 hf'0 (by simp)
  refine ⟨s * g⁻¹, ?_, ?_⟩
  · have hg' : ((g⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
      VecStab.mem_vecStab.mp ((VecStab.vecStab _).inv_mem hg)
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg', hs]
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← hf']
    rw [← hgf]
    rfl

theorem inv_transpose_mulVec_iff (A : SL4) (f : Fin 4 → ZMod 2) :
    ((A⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f = f ↔
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f = f := by
  have h1 : ∀ B : SL4, (B : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ
      (((B⁻¹ : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ f) = f := fun B => by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.one_mulVec]
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact h1 A
  · intro h
    have := h1 A⁻¹
    rwa [inv_inv, h] at this

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem mem_centralizer_iff₂ {w : G} (hw : w ∈ V₂) (l : ↥L) :
    (l : G) ∈ Subgroup.centralizer ({w} : Set G) ↔
      (c.S.C₂.ρ l : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c.S.C₂.E w = c.S.C₂.E w := by
  rw [← c.S.C₂.conj l w hw, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    have h1 := c.S.C₂.inj _ (c.S.C₂.conj_mem l hw) _ hw h
    calc (l : G) * w = ((l : G) * w * (l : G)⁻¹) * l := by group
      _ = w * l := by rw [h1]

end Setting

omit [Finite G] in
theorem rho_eq_one {L W : Subgroup G} (C : KGH91.NatCoord L W 4) {y : ↥L}
    (hy : ∀ a ∈ W, (y : G) * a * (y : G)⁻¹ = a) : C.ρ y = 1 := by
  apply Subtype.ext
  ext i j
  obtain ⟨a, ha, hae⟩ := C.surj (Pi.single j 1)
  have h1 := C.conj y a ha
  rw [hy a ha, hae, Matrix.mulVec_single_one] at h1
  have := congrFun h1 i
  simp only [Matrix.col_apply] at this
  rw [Matrix.SpecialLinearGroup.coe_one, ← this, Matrix.one_apply, Pi.single_apply]

end CFSG.Quasithin.H13.Sec1214
