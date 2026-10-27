module

public import CFSG.Quasithin.Background.G25Dual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def stab0 (F : Type) [Field F] : Subgroup SL(3, F) where
  carrier := {A | A • vE F 0 = vE F 0}
  one_mem' := one_smul _ _
  mul_mem' := fun {A B} hA hB => by
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    rw [mul_smul, hB, hA]
  inv_mem' := fun {A} hA => by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    rw [inv_smul_eq_iff, hA]

theorem stab0_col {A : SL(3, F)} (h : A ∈ stab0 F) :
    A.1 0 0 = 1 ∧ A.1 1 0 = 0 ∧ A.1 2 0 = 0 := by
  have e := fun i => smul_single_one A 0 i
  have hA : A • vE F 0 = vE F 0 := h
  refine ⟨?_, ?_, ?_⟩
  · have := e 0
    rw [hA] at this
    simpa using this.symm
  · have := e 1
    rw [hA] at this
    simpa using this.symm
  · have := e 2
    rw [hA] at this
    simpa using this.symm

@[expose] def leviMat (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![A 1 1, A 1 2; A 2 1, A 2 2]

theorem det_leviMat {A : SL(3, F)} (h : A ∈ stab0 F) : (leviMat A.1).det = 1 := by
  obtain ⟨h0, h1, h2⟩ := stab0_col h
  have hdet := A.2
  rw [Matrix.det_fin_three, h0, h1, h2] at hdet
  rw [leviMat, Matrix.det_fin_two_of]
  linear_combination hdet

theorem leviMat_mul {A B : SL(3, F)} (h : A ∈ stab0 F) :
    leviMat (A * B).1 = leviMat A.1 * leviMat B.1 := by
  obtain ⟨-, h1, h2⟩ := stab0_col h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two, h1, h2]

@[expose] def levi (F : Type) [Field F] : ↥(stab0 F) →* SL(2, F) where
  toFun A := ⟨leviMat A.1.1, det_leviMat A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leviMat]
  map_mul' A B := Subtype.ext (leviMat_mul A.2)

theorem levi_coe (A : ↥(stab0 F)) : ((levi F A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![A.1.1 1 1, A.1.1 1 2; A.1.1 2 1, A.1.1 2 2] := rfl

theorem blk_mem_stab0 (M : SL(2, F)) : blk M ∈ stab0 F := by
  show blk M • vE F 0 = vE F 0
  ext i
  rw [smul_single_one]
  fin_cases i <;> simp [blk_coe]

theorem levi_blk (M : SL(2, F)) : levi F ⟨blk M, blk_mem_stab0 M⟩ = M := by
  apply Subtype.ext
  rw [levi_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk_coe]

theorem mem_Qv_of_levi_eq_one {A : ↥(stab0 F)} (h : levi F A = 1) :
    (A : SL(3, F)) ∈ Qv (vE F 0) := by
  obtain ⟨h0, h1, h2⟩ := stab0_col A.2
  have hM := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F)) h
  simp only [levi_coe, Matrix.SpecialLinearGroup.coe_one] at hM
  have e11 : A.1.1 1 1 = 1 := by simpa using congrFun (congrFun hM 0) 0
  have e12 : A.1.1 1 2 = 0 := by simpa using congrFun (congrFun hM 0) 1
  have e21 : A.1.1 2 1 = 0 := by simpa using congrFun (congrFun hM 1) 0
  have e22 : A.1.1 2 2 = 1 := by simpa using congrFun (congrFun hM 1) 1
  rw [mem_Qv_e0]
  refine ⟨A.1.1 0 1, A.1.1 0 2, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tq_coe, h0, h1, h2, e11, e12, e21, e22]

theorem mul_blk_inv_mem_Qv (A : ↥(stab0 F)) :
    (A : SL(3, F)) * (blk (levi F A))⁻¹ ∈ Qv (vE F 0) := by
  have hmem : (A : SL(3, F)) * (blk (levi F A))⁻¹ ∈ stab0 F :=
    (stab0 F).mul_mem A.2 ((stab0 F).inv_mem (blk_mem_stab0 _))
  have h1 : levi F ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥(stab0 F)) = A * (⟨blk (levi F A), blk_mem_stab0 _⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, levi_blk, mul_inv_cancel]
  exact mem_Qv_of_levi_eq_one h1

theorem levi_smul (A : ↥(stab0 F)) (w : Fin 3 → F) :
    ![((A : SL(3, F)) • w) 1, ((A : SL(3, F)) • w) 2] = levi F A • ![w 1, w 2] := by
  obtain ⟨-, h1, h2⟩ := stab0_col A.2
  ext i
  fin_cases i <;>
    simp [Matrix.SpecialLinearGroup.smul_def, levi_coe, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem levi_inv_coe (A : ↥(stab0 F)) :
    ((levi F A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.adjugate ((levi F A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  rw [map_inv, Matrix.SpecialLinearGroup.coe_inv]

theorem levi_dual_smul [CharP F 2] (A : ↥(stab0 F)) (φ : Fin 3 → F) (hφ : φ 0 = 0) :
    (CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) 0 = 0 ∧
      ![(CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) 2,
        (CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) 1] = levi F A • ![φ 2, φ 1] := by
  set B : ↥(stab0 F) := A⁻¹ with hB
  obtain ⟨-, hB1, hB2⟩ := stab0_col B.2
  have hinv := levi_inv_coe A
  rw [← hB, levi_coe, levi_coe, Matrix.adjugate_fin_two] at hinv
  have b11 : B.1.1 1 1 = A.1.1 2 2 := by simpa using congrFun (congrFun hinv 0) 0
  have b12 : B.1.1 1 2 = A.1.1 1 2 := by
    have := congrFun (congrFun hinv 0) 1
    simpa [CharTwo.neg_eq] using this
  have b21 : B.1.1 2 1 = A.1.1 2 1 := by
    have := congrFun (congrFun hinv 1) 0
    simpa [CharTwo.neg_eq] using this
  have b22 : B.1.1 2 2 = A.1.1 1 1 := by simpa using congrFun (congrFun hinv 1) 1
  have hd : ∀ i, (CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) i =
      ∑ k, (B : SL(3, F)).1 k i * φ k := by
    intro i
    rw [dualHom_apply, Matrix.SpecialLinearGroup.smul_def, slT_coe]
    show ∑ k, ((↑((A : SL(3, F))⁻¹) : Matrix (Fin 3) (Fin 3) F))ᵀ i k * φ k = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hd, Fin.sum_univ_three, hφ, hB1, hB2]
    ring
  · ext i
    fin_cases i
    · show (CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) 2 = (levi F A • ![φ 2, φ 1]) 0
      rw [hd, Fin.sum_univ_three, hφ, Matrix.SpecialLinearGroup.smul_def, levi_coe]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, b12, b22]
      ring
    · show (CFSG.Quasithin.dualHom F 3 (A : SL(3, F)) • φ) 1 = (levi F A • ![φ 2, φ 1]) 1
      rw [hd, Fin.sum_univ_three, hφ, Matrix.SpecialLinearGroup.smul_def, levi_coe]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, b11, b21]
      ring

theorem conj_qhom [CharP F 2] (A : ↥(stab0 F)) (q : Wm F) :
    (A : SL(3, F)) * qhom q * (A : SL(3, F))⁻¹ = qhom (SL2Model.natAct (levi F A) q) := by
  set Q₀ := (A : SL(3, F)) * (blk (levi F A))⁻¹ with hQ₀
  have hQ := mul_blk_inv_mem_Qv A
  have hA : (A : SL(3, F)) = Q₀ * blk (levi F A) := by rw [hQ₀, inv_mul_cancel_right]
  have hq' : qhom (SL2Model.natAct (levi F A) q) ∈ Qv (vE F 0) := by
    rw [← qhom_range]
    exact ⟨_, rfl⟩
  rw [hA, _root_.mul_inv_rev, show Q₀ * blk (levi F A) * qhom q * ((blk (levi F A))⁻¹ * Q₀⁻¹) =
      Q₀ * (blk (levi F A) * qhom q * (blk (levi F A))⁻¹) * Q₀⁻¹ by group, blk_qhom,
    Qv_comm _ _ hQ hq', mul_inv_cancel_right]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
