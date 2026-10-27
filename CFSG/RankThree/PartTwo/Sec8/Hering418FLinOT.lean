module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofGL3
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

theorem congr_eq_mul_mul_inv {M : Type*} [Group M] (f τ : MulAut M) :
    MulAut.congr f τ = f * τ * f⁻¹ := by
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_def]

section OT

variable {F : Type} [Field F]

theorem sl_ext {n : ℕ} {A B : SpecialLinearGroup (Fin n) F}
    (h : (A : Matrix (Fin n) (Fin n) F) = B) : A = B :=
  Subtype.ext h

theorem pow_three_eq_one_of_mem_scalars {z : SpecialLinearGroup (Fin 3) F} (hz : z ∈ scalars 3 F) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc, hzc⟩ := hz
  refine sl_ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, hzc, ← map_pow, Matrix.SpecialLinearGroup.coe_one,
    ← Units.val_pow_eq_pow_val, hc]
  simp

theorem eq_one_of_conj_fixed_psl3 [Finite F] [CharP F 2] {y u : projectiveSL 3 F}
    (hy3 : (MulAut.conj y : MulAut (projectiveSL 3 F)) ^ 3 = 1) (hyu : y * u * y⁻¹ = u)
    (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : y = 1 := by
  have hy3' : y ^ 3 = 1 := by
    have h1 : y ^ 3 ∈ Subgroup.center (projectiveSL 3 F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut (projectiveSL 3 F) => f g) hy3
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [Sec21.Item223CensusResProof.center_projectiveSL_three F] at h1
    exact h1
  obtain ⟨A, rfl⟩ := proj_surjective 3 F y
  obtain ⟨B, rfl⟩ := proj_surjective 3 F u
  have hA3 : A ^ 3 ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact hy3'
  have hB4 : B ^ 4 ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact hu4
  have hB2 : B ^ 2 ∉ scalars 3 F := by
    intro h
    apply hu2
    rw [← map_pow]
    exact proj_eq_one_iff.mpr h
  have hAB : ∃ z ∈ scalars 3 F, A * B * A⁻¹ = B * z := by
    have h : proj 3 F (A * B * A⁻¹) = proj 3 F B := by
      rw [map_mul, map_mul, map_inv]
      exact hyu
    refine ⟨((A * B * A⁻¹)⁻¹ * B)⁻¹, inv_mem (proj_eq_proj_iff.mp h), ?_⟩
    group
  obtain ⟨z, hz, hABz⟩ := hAB
  have hzc : Commute B z :=
    ((Subgroup.mem_center_iff.mp ((scalars_eq_center 3 F) ▸ hz)) B)
  have hAB3 : A * B ^ 3 = B ^ 3 * A := by
    have h1 : A * B ^ 3 * A⁻¹ = (A * B * A⁻¹) ^ 3 := by
      rw [conj_pow]
    rw [hABz, hzc.mul_pow, pow_three_eq_one_of_mem_scalars hz, mul_one] at h1
    calc A * B ^ 3 = A * B ^ 3 * A⁻¹ * A := by group
      _ = B ^ 3 * A := by rw [h1]
  have hB12 : (B ^ 3) ^ 4 = 1 := by
    obtain ⟨c, hc, hBc⟩ := hB4
    refine sl_ext ?_
    rw [← pow_mul, show 3 * 4 = 4 * 3 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hBc,
      ← map_pow, Matrix.SpecialLinearGroup.coe_one, ← Units.val_pow_eq_pow_val, hc]
    simp
  have hB6 : (B ^ 3) ^ 2 ≠ 1 := by
    intro h
    apply hB2
    obtain ⟨c, hc, hBc⟩ := hB4
    have h6 : B ^ 6 = 1 := by rw [← pow_mul] at h; exact h
    have h2 : B ^ 2 = (B ^ 4)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add]
      exact h6
    rw [h2]
    exact inv_mem ⟨c, hc, hBc⟩
  have hAGL : (SpecialLinearGroup.toGL A) ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by
    obtain ⟨c, hc, hAc⟩ := hA3
    rw [← map_pow, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    exact hAc.symm
  have hcomm : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL (B ^ 3) =
      SpecialLinearGroup.toGL (B ^ 3) * SpecialLinearGroup.toGL A := by
    rw [← map_mul, ← map_mul, hAB3]
  have h4 : (SpecialLinearGroup.toGL (B ^ 3)) ^ 4 = 1 := by
    rw [← map_pow, hB12, map_one]
  have h2 : (SpecialLinearGroup.toGL (B ^ 3)) ^ 2 ≠ 1 := by
    intro h
    apply hB6
    rw [← map_pow] at h
    exact SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm)
  have hAc := Item8KFacts2Proof.mem_center_of_commute hAGL hcomm h4 h2
  have hAcen : A ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := (Subgroup.mem_center_iff.mp hAc) (SpecialLinearGroup.toGL g)
    rw [← map_mul, ← map_mul] at this
    exact SpecialLinearGroup.toGL_injective this
  rw [← scalars_eq_center] at hAcen
  exact proj_eq_one_iff.mpr hAcen

end OT

section Unip

variable (F : Type) [Field F]

@[expose] def unipElem : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def unipProj : projectiveSL 3 F := proj 3 F (unipElem F)

variable {F}

theorem coe_unipElem : (unipElem F : Matrix (Fin 3) (Fin 3) F) = !![1, 1, 0; 0, 1, 1; 0, 0, 1] :=
  rfl

theorem map_unipElem {F' : Type} [Field F'] (f : F →+* F') :
    SpecialLinearGroup.map f (unipElem F) = unipElem F' := by
  refine sl_ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_unipElem, coe_unipElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem fieldAut_unipProj (τ : F ≃+* F) : fieldAut 3 F τ (unipProj F) = unipProj F := by
  unfold unipProj
  rw [fieldAut_proj, map_unipElem]

variable [CharP F 2]

theorem coe_unipElem_sq :
    ((unipElem F ^ 2 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  have h2 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharTwo.two_eq_zero
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_unipElem]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem unipElem_pow_four : unipElem F ^ 4 = 1 := by
  have h2 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharTwo.two_eq_zero
  refine sl_ext ?_
  rw [show 4 = 2 * 2 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, coe_unipElem_sq,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem unipElem_sq_not_mem_scalars : unipElem F ^ 2 ∉ scalars 3 F := by
  rintro ⟨c, -, hc⟩
  rw [coe_unipElem_sq] at hc
  have h := congrFun (congrFun hc 0) 2
  simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h

theorem unipProj_pow_four : unipProj F ^ 4 = 1 := by
  unfold unipProj
  rw [← map_pow, unipElem_pow_four, map_one]

theorem unipProj_sq_ne_one : unipProj F ^ 2 ≠ 1 := by
  unfold unipProj
  rw [← map_pow]
  intro h
  exact unipElem_sq_not_mem_scalars (proj_eq_one_iff.mp h)

end Unip

end CFSG.RankThree.PartTwo.Sec8.Hering418
