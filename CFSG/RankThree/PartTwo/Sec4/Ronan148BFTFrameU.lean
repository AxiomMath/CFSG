module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTModelU
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F]

theorem cycThree_mem_unitarySU (hU : UnitaryFieldData 2 f F) :
    (cycThree : GL (Fin 3) F) ∈ unitarySU 2 f F 3 := by
  rw [mem_unitarySU_iff hU]
  have hP : ((cycThree : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map hU.bar =
      ((cycThree : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rw [Matrix.map_apply, coe_cycThree]
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨?_, ?_⟩
  · rw [coe_cycThree, Matrix.det_fin_three]
    simp
  · rw [hP, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem diagTau_mem_unitarySU (hU : UnitaryFieldData 2 f F) (hf : Odd f) {τ : F}
    (hτ : τ ^ 3 = 1) : diagTau hτ ∈ unitarySU 2 f F 3 := by
  have hK : PiField false 2 f F := ⟨Nat.prime_two, hU.one_le, hU.card_eq_sq⟩
  have hq : ModThree false (2 ^ f) := two_pow_mod_three_of_odd_ftU hf
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  rw [diagTau_eq_diagUnits hτ hτ0, mem_unitarySU_iff hU]
  have hτu : Units.mk0 τ hτ0 ∈ rootsOfUnity (qSubPi false (2 ^ f)) F :=
    cube_root_mem_qSubPi hq (by
      rw [mem_rootsOfUnity]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hτ, Units.val_one]))
  have hH := diagUnits_mem_glPi hK hτu (pow_mem hτu 2) (one_mem _)
  refine ⟨?_, (mem_glPi_false hU).mp hH⟩
  rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_one, mul_one]
  linear_combination hτ

theorem fourierGL_mem_unitarySU (hU : UnitaryFieldData 2 f F) (hf : Odd f) {τ : F}
    (hτ : τ ^ 3 = 1) (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0) :
    fourierGL h3 hs ∈ unitarySU 2 f F 3 :=
  fourierGL_mem_slPi (π := false) ⟨Nat.prime_two, hU.one_le, hU.card_eq_sq⟩
    (two_pow_mod_three_of_odd_ftU hf) hτ h3 hs

theorem phaseGL_mem_unitaryIsom3 (hU : UnitaryFieldData 2 f F) (hf : Odd f) {τ : F}
    (hτ : τ ^ 3 = 1) : phaseGL hτ ∈ unitaryIsom3 hU :=
  (mem_glPi_false hU).mp (phaseGL_mem_glPi (π := false)
    ⟨Nat.prime_two, hU.one_le, hU.card_eq_sq⟩ (two_pow_mod_three_of_odd_ftU hf) hτ)

theorem glAut_diagTau (ρ : F ≃+* F) {τ : F} (hτ : τ ^ 3 = 1) (hρ : ρ τ = τ) :
    glAut ρ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_glAut, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hρ]

theorem glAut_fourierGL (ρ : F ≃+* F) {τ : F} (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0)
    (hρ : ρ τ = τ) : glAut ρ (fourierGL h3 hs) = fourierGL h3 hs := by
  apply Units.ext
  rw [coe_glAut, coe_fourierGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMat, hρ, map_inv₀]

theorem glAut_phaseGL (ρ : F ≃+* F) {τ : F} (hτ : τ ^ 3 = 1) (hρ : ρ τ = τ) :
    glAut ρ (phaseGL hτ) = phaseGL hτ := by
  apply Units.ext
  rw [coe_glAut, coe_phaseGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hρ]

section Relations

variable {τ : F} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) (h3 : (3 : F) ≠ 0) (hs : 1 + τ + τ ^ 2 = 0)

include hs in
theorem fourierGL_mul_diagTau :
    fourierGL h3 hs * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cycThree⁻¹ * fourierGL h3 hs) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_fourierGL,
    coe_diagTau, coe_cycThree_inv, Units.val_mk0, scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMat, mul_apply, Fin.sum_univ_three] <;> grind

include hs in
theorem fourierGL_mul_cycThree :
    fourierGL h3 hs * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (diagTau hτ * fourierGL h3 hs) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_fourierGL,
    coe_diagTau, coe_cycThree, Units.val_pow_eq_pow_val, Units.val_mk0, scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fourierMat, mul_apply, Fin.sum_univ_three] <;> grind

theorem phaseGL_mul_cycThree :
    phaseGL hτ * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) *
        (diagTau hτ * cycThree * phaseGL hτ) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
    coe_phaseGL, coe_diagTau, coe_cycThree, Units.val_mk0, scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> grind

theorem phaseGL_mul_diagTau : phaseGL hτ * diagTau hτ = diagTau hτ * phaseGL hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_phaseGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

end Relations

variable {hU : UnitaryFieldData 2 f F}

theorem unitaryProj_eq_mk (M : unitarySU 2 f F 3) :
    unitaryProj hU 3 M = (M : unitaryPSU hU 3) := rfl

theorem inv_mul_glAut_mem (ρ : F ≃+* F) {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU) :
    W⁻¹ * glAut ρ W ∈ unitaryIsom3 hU :=
  mul_mem (inv_mem hW) (glAut_mem_unitaryIsom3 ρ hW)

theorem psuField_frame (ρ : F ≃+* F) {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU)
    (x : unitaryPSU hU 3) :
    psuField hU ρ (psuConj hU ⟨W, hW⟩ x) =
      psuConj hU ⟨W, hW⟩ (psuConj hU ⟨_, inv_mul_glAut_mem ρ hW⟩ (psuField hU ρ x)) := by
  induction x using QuotientGroup.induction_on with
  | H M =>
    rw [psuConj_mk, psuField_mk, psuField_mk, psuConj_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    simp only [coe_suField, coe_suConj, Subgroup.coe_inv, map_mul, map_inv]
    group

theorem twist_frame (ρ : F ≃+* F) {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU)
    (zh : unitarySU 2 f F 3) (x : unitaryPSU hU 3) :
    psuField hU ρ ((zh : unitaryPSU hU 3) * psuConj hU ⟨W, hW⟩ x * (zh : unitaryPSU hU 3)⁻¹) =
      psuConj hU ⟨W, hW⟩ (psuConj hU ⟨W⁻¹ * glAut ρ ((zh : GL (Fin 3) F) * W), mul_mem (inv_mem hW)
        (glAut_mem_unitaryIsom3 ρ (mul_mem (unitarySU_le_unitaryIsom3 zh.2) hW))⟩
          (psuField hU ρ x)) := by
  induction x using QuotientGroup.induction_on with
  | H M =>
    rw [psuConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      psuField_mk, psuField_mk, psuConj_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    simp only [coe_suField, coe_suConj, Subgroup.coe_inv, Subgroup.coe_mul, map_mul, map_inv]
    group

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
