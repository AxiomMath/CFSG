module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Groups
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev l43Mat : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

abbrev l43SL : Type := Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)

@[expose] def l43G01 : l43Mat := !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def l43G12 : l43Mat := !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def l43G23 : l43Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def l43Z (c : ZMod 3) : l43Mat := !![1, 0, 0, c; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def l43N (c : ZMod 3) : l43Mat := !![1, 0, -c, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def l43S : l43Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

@[expose] def l43Si : l43Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

theorem det_of_unitri (A : l43Mat) (hlow : ∀ i j : Fin 4, j < i → A i j = 0)
    (hdiag : ∀ i : Fin 4, A i i = 1) : A.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, hdiag]
  · intro i j hij
    exact hlow i j hij

theorem l43G01_unitri : ∀ i j : Fin 4, j < i → l43G01 i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [l43G01]

theorem l43G01_diag : ∀ i : Fin 4, l43G01 i i = 1 := by
  intro i
  fin_cases i <;> simp [l43G01]

theorem l43G12_unitri : ∀ i j : Fin 4, j < i → l43G12 i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [l43G12]

theorem l43G12_diag : ∀ i : Fin 4, l43G12 i i = 1 := by
  intro i
  fin_cases i <;> simp [l43G12]

theorem l43G23_unitri : ∀ i j : Fin 4, j < i → l43G23 i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [l43G23]

theorem l43G23_diag : ∀ i : Fin 4, l43G23 i i = 1 := by
  intro i
  fin_cases i <;> simp [l43G23]

theorem l43N_unitri : ∀ c : ZMod 3, ∀ i j : Fin 4, j < i → l43N c i j = 0 := by
  intro c i j hij
  fin_cases i <;> fin_cases j <;> simp_all [l43N]

theorem l43N_diag : ∀ c : ZMod 3, ∀ i : Fin 4, l43N c i i = 1 := by
  intro c i
  fin_cases i <;> simp [l43N]

theorem det_l43G01 : l43G01.det = 1 := det_of_unitri l43G01 l43G01_unitri l43G01_diag

theorem det_l43G12 : l43G12.det = 1 := det_of_unitri l43G12 l43G12_unitri l43G12_diag

theorem det_l43G23 : l43G23.det = 1 := det_of_unitri l43G23 l43G23_unitri l43G23_diag

theorem det_l43N (c : ZMod 3) : (l43N c).det = 1 :=
  det_of_unitri (l43N c) (l43N_unitri c) (l43N_diag c)

theorem det_l43S : l43S.det = 1 := by
  simp [l43S, Matrix.det_succ_row_zero, Fin.sum_univ_succ] <;> decide

theorem det_l43Si : l43Si.det = 1 := by
  simp [l43Si, Matrix.det_succ_row_zero, Fin.sum_univ_succ] <;> decide

@[expose] def l43RG01 : l43SL := ⟨l43G01, det_l43G01⟩

@[expose] def l43RG12 : l43SL := ⟨l43G12, det_l43G12⟩

@[expose] def l43RG23 : l43SL := ⟨l43G23, det_l43G23⟩

@[expose] def l43NSL (c : ZMod 3) : l43SL := ⟨l43N c, det_l43N c⟩

@[expose] def l43SSL : l43SL := ⟨l43S, det_l43S⟩

@[expose] def l43SiSL : l43SL := ⟨l43Si, det_l43Si⟩

theorem l43NSL_val (c : ZMod 3) : ((l43NSL c : l43SL) : l43Mat) = l43N c := rfl

theorem l43SSL_val : ((l43SSL : l43SL) : l43Mat) = l43S := rfl

theorem l43SiSL_val : ((l43SiSL : l43SL) : l43Mat) = l43Si := rfl

theorem l43RG01_mem : l43RG01 ∈ unitriangular 4 (ZMod 3) :=
  mem_unitriangular.mpr ⟨l43G01_unitri, l43G01_diag⟩

theorem l43RG12_mem : l43RG12 ∈ unitriangular 4 (ZMod 3) :=
  mem_unitriangular.mpr ⟨l43G12_unitri, l43G12_diag⟩

theorem l43RG23_mem : l43RG23 ∈ unitriangular 4 (ZMod 3) :=
  mem_unitriangular.mpr ⟨l43G23_unitri, l43G23_diag⟩

theorem l43Z_zero : l43Z 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l43Z, Matrix.one_apply]

theorem l43S_mul_Si : l43S * l43Si = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, l43S, l43Si,
    Matrix.one_apply] <;> decide

theorem l43S_mul_Z (c : ZMod 3) : l43S * l43Z c * l43Si = l43N c := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, l43S, l43Z, l43Si, l43N] <;> decide

theorem l43N_mul_Z (c : ZMod 3) : l43N c * l43Z c = l43Z c * l43N c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, l43N, l43Z]

theorem l43N_mul_Ninv (c : ZMod 3) : l43N c * l43N (-c) = 1 := by
  fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, l43N, Matrix.one_apply] <;> decide

theorem inv_l43NSL (c : ZMod 3) : (l43NSL c)⁻¹ = l43NSL (-c) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, l43NSL_val, Matrix.SpecialLinearGroup.coe_one]
  exact l43N_mul_Ninv c

theorem upper_of_comm_roots (A : l43Mat) (h01 : l43G01 * A = A * l43G01)
    (h12 : l43G12 * A = A * l43G12) (h23 : l43G23 * A = A * l43G23) :
    A 0 1 = 0 ∧ A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 1 3 = 0 ∧ A 2 3 = 0 := by
  have e1 := congrFun (congrFun h01 0) 2
  have e2 := congrFun (congrFun h01 0) 3
  have e3 := congrFun (congrFun h12 0) 2
  have e4 := congrFun (congrFun h12 1) 3
  have e5 := congrFun (congrFun h23 0) 3
  have e6 := congrFun (congrFun h23 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, l43G01, l43G12, l43G23] at e1 e2 e3 e4 e5 e6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · first | linear_combination e3 | linear_combination -e3
  · first | linear_combination e5 | linear_combination -e5
  · first | linear_combination e6 | linear_combination -e6
  · first | linear_combination e2 | linear_combination -e2
  · first | linear_combination e4 | linear_combination -e4

theorem eq_l43Z_of (A : l43Mat) (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) (h21 : A 2 1 = 0)
    (h30 : A 3 0 = 0) (h31 : A 3 1 = 0) (h32 : A 3 2 = 0)
    (d0 : A 0 0 = 1) (d1 : A 1 1 = 1) (d2 : A 2 2 = 1) (d3 : A 3 3 = 1)
    (h01 : A 0 1 = 0) (h02 : A 0 2 = 0) (h12 : A 1 2 = 0) (h13 : A 1 3 = 0)
    (h23 : A 2 3 = 0) : A = l43Z (A 0 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l43Z, h10, h20, h21, h30, h31, h32, d0, d1, d2, d3, h01, h02, h12, h13, h23]

theorem scalar_entry_zero (X : l43SL) (hX : X ∈ scalars 4 (ZMod 3)) :
    (X : l43Mat) 0 2 = 0 := by
  rcases Item434RemL43.val_eq_one_or_neg_one_of_mem_scalars hX with h | h
  · rw [h]; simp <;> decide
  · rw [h]; simp <;> decide

end CFSG.RankThree.PartTwo.Sec4.RonanK432
