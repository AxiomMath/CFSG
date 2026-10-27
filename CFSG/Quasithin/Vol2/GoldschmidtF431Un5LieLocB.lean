module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocA
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3FusionLevi

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def slM (A : SpecialLinearGroup (Fin 2) h.fixedField) : Matrix (Fin 2) (Fin 2) K :=
  ((slF h A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

theorem slM_apply (A : SpecialLinearGroup (Fin 2) h.fixedField) (i j : Fin 2) :
    slM A i j = ((A : Matrix (Fin 2) (Fin 2) h.fixedField) i j : K) := rfl

theorem det_slM (A : SpecialLinearGroup (Fin 2) h.fixedField) : (slM A).det = 1 := by
  have := (slF h A).det_coe
  exact this

theorem isUnit_det_slM (A : SpecialLinearGroup (Fin 2) h.fixedField) : IsUnit (slM A).det := by
  rw [det_slM]
  exact isUnit_one

theorem bar_slM (A : SpecialLinearGroup (Fin 2) h.fixedField) (i j : Fin 2) :
    h.bar (slM A i j) = slM A i j :=
  h.mem_fixedField.1 (A i j).2

theorem map_bar_slM (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    (slM A).map h.bar = slM A := by
  ext i j
  exact bar_slM A i j

theorem levHom_eq_lev (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h A = lev (hK := h) (slM A) (isUnit_det_slM A) := by
  apply mat_injective
  rw [mat_lev, det_slM, map_one, div_one]
  rw [levHom, MonoidHom.comp_apply, mat_leviSU, oddDiag]
  congr 1
  · ext k l
    fin_cases k
    fin_cases l
    simp
  · refine eq_barInvT_of_mul_eq_one ?_
    have := UnitaryHigher.bar_map_mul_inv h (SpecialLinearGroup.toGL (slF h A))
    rwa [SpecialLinearGroup.coe_GL_coe_matrix] at this

theorem Yof_levHom_conj (A : SpecialLinearGroup (Fin 2) h.fixedField) {v : hypSU h 2 1}
    (hv : v ∈ Vsub h) : levHom h A * v * (levHom h A)⁻¹ ∈ Vsub h ∧
      Yof (levHom h A * v * (levHom h A)⁻¹) = slM A * Yof v * (slM A)ᵀ := by
  rw [levHom_eq_lev]
  have := lev_conj_Yof h (slM A) (isUnit_det_slM A) hv
  rwa [map_bar_slM] at this

theorem mul_J_mul_transpose [CharP K 2] {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1) :
    M * !![0, 1; 1, 0] * Mᵀ = !![0, 1; 1, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (M 0 0 * M 0 1) * h2
  · linear_combination hM + (M 0 1 * M 1 0) * h2
  · linear_combination hM + (M 0 1 * M 1 0) * h2
  · linear_combination (M 1 0 * M 1 1) * h2

theorem levHom_conj_z₂SU [CharP K 2] (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h A * z₂SU h * (levHom h A)⁻¹ = z₂SU h := by
  obtain ⟨hmem, hY⟩ := Yof_levHom_conj A (vSU_mem_Vsub (isHerm_swap h) : z₂SU h ∈ Vsub h)
  refine Yof_injOn h hmem (vSU_mem_Vsub (isHerm_swap h)) ?_
  rw [hY]
  have : Yof (z₂SU h) = !![0, 1; 1, 0] := Yof_vSU (isHerm_swap h)
  rw [this]
  exact mul_J_mul_transpose (det_slM A)

end CFSG.Quasithin.H13.F431.Un.L5
