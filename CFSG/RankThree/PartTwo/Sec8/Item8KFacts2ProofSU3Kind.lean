module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofGL3
public import CFSG.RankThree.PartTwo.KFacts.K71SU3Normal
public import CFSG.RankThree.PartOne.SEITZQ1.Plane

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {f : ℕ} {F : Type} [Field F]

theorem eq_one_of_suConj_of_fixed (h : UnitaryFieldData 2 f F) (hf : Odd f)
    {A : unitaryIsom3 h} (hA3 : suConj h A ^ 3 = 1) {u : unitarySU 2 f F 3}
    (hu : suConj h A u = u) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : suConj h A = 1 := by
  have : CharP F 2 := h.charP
  obtain ⟨ω, hω, -⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h hf
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have : (3 : F) = 0 := by linear_combination hω
    have h1 : (1 : F) = 0 := by linear_combination this - h2F
    exact one_ne_zero h1
  have hmod : Sec4.ModThree false (2 ^ f) := by
    obtain ⟨k, rfl⟩ := hf
    change 2 ^ (2 * k + 1) % 3 = 2
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hA3c : ((A : GL (Fin 3) F) ^ 3) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine Sec4.mem_statedScalars_of_commute (π := false) (fun _ => h) (fun _ => hmod) hω3 hω1
      fun x hx => ?_
    have h1 := DFunLike.congr_fun hA3 ⟨x, hx⟩
    rw [← map_pow, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_suConj] at h2
    change ((A ^ 3 : unitaryIsom3 h) : GL (Fin 3) F) * x *
      ((A ^ 3 : unitaryIsom3 h) : GL (Fin 3) F)⁻¹ = x at h2
    rw [Subgroup.coe_pow] at h2
    calc (A : GL (Fin 3) F) ^ 3 * x = (A : GL (Fin 3) F) ^ 3 * x *
          ((A : GL (Fin 3) F) ^ 3)⁻¹ * (A : GL (Fin 3) F) ^ 3 := by group
      _ = x * (A : GL (Fin 3) F) ^ 3 := by rw [h2]
  have hAu : (A : GL (Fin 3) F) * u = u * A := by
    have h1 := congrArg Subtype.val hu
    rw [coe_suConj, Subgroup.coe_inv] at h1
    calc (A : GL (Fin 3) F) * u = (A : GL (Fin 3) F) * u * (A : GL (Fin 3) F)⁻¹ * A := by
          group
      _ = u * A := by rw [h1]
  have hu4' : ((u : GL (Fin 3) F)) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, hu4, Subgroup.coe_one]
  have hu2' : ((u : GL (Fin 3) F)) ^ 2 ≠ 1 := by
    intro h1
    apply hu2
    apply Subtype.ext
    rw [Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hAc := mem_center_of_commute hA3c hAu hu4' hu2'
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_suConj, MulAut.one_apply, Subgroup.coe_inv, (Subgroup.mem_center_iff.mp hAc g).symm,
    mul_inv_cancel_right]

theorem hasKind_field_of_fixed_order_four [Finite F] (h : UnitaryFieldData 2 f F) (hf : Odd f)
    (hq : 2 < 2 ^ f) {β : MulAut (unitarySU 2 f F 3)} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {u : unitarySU 2 f F 3} (hu : β u = u) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) :
    (stdPinnedPSU3 h).HasKind (suDescend h hq β) .field := by
  have hα3 : (suDescend h hq β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  by_cases hD : suDescend h hq β ∈ (psuConj h).range
  · exfalso
    obtain ⟨A, hA⟩ := hD
    have hβA : β = suConj h A := eq_of_suDescend_eq h hq (by rw [suDescend_suConj, hA])
    subst hβA
    exact hβ1 (eq_one_of_suConj_of_fixed h hf hβ3 hu hu4 hu2)
  · exact (PinnedAut.hasKind_field _).mpr (isField_psu3_of_pow_three_eq_one hq hα3 hD)


@[expose] def fourierMat (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

theorem exists_unitarySU_pow_four (h : UnitaryFieldData 2 f F) (hf : Odd f) :
    ∃ u : unitarySU 2 f F 3, u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
  have : CharP F 2 := h.charP
  obtain ⟨ω, hω, hbar⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h hf
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by grind
  have hω4 : ω ^ 4 = ω := by grind
  have hbar2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hbar]
    grind
  have hdet : (fourierMat ω).det = 1 := by
    rw [fourierMat, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    grind
  have hdet0 : (fourierMat ω).det ≠ 0 := by rw [hdet]; exact one_ne_zero
  set M : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (fourierMat ω) hdet0 with hM
  have hMval : (M : Matrix (Fin 3) (Fin 3) F) = fourierMat ω := rfl
  have hMu : M ∈ unitarySU 2 f F 3 := by
    refine (mem_unitarySU_iff h).2 ⟨hdet, ?_⟩
    rw [hMval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.transpose_apply, hbar, hbar2] <;>
      grind
  have hsq : fourierMat ω * fourierMat ω = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
      grind
  have hP : (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hM2 : ((M ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
    rw [Units.val_pow_eq_pow_val, hMval, sq, hsq]
  refine ⟨⟨M, hMu⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_one, show (4 : ℕ) = 2 * 2 by rfl, pow_mul,
      Units.val_pow_eq_pow_val, hM2, sq, hP]
  · intro h1
    have h2 := congrArg (fun x : unitarySU 2 f F 3 =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_one] at h2
    rw [hM2] at h2
    simp at h2

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
