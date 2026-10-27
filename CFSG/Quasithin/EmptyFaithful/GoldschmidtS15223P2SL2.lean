module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.S15223

open Matrix

variable {F : Type*} [Field F]

@[expose] def sl2U (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2L (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2W [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem sl2U_mul (a b : F) : sl2U a * sl2U b = sl2U (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2U, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2U_zero : sl2U (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2U]

theorem sl2U_mul_self [CharP F 2] (a : F) : sl2U a * sl2U a = 1 := by
  rw [sl2U_mul, CharTwo.add_self_eq_zero, sl2U_zero]

theorem sl2W_mul_self [CharP F 2] : (sl2W : SpecialLinearGroup (Fin 2) F) * sl2W = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2W, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2W_mul_sl2U_mul_sl2W [CharP F 2] (a : F) :
    (sl2W : SpecialLinearGroup (Fin 2) F) * sl2U a * sl2W = sl2L a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2W, sl2U, sl2L, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2U_mul_sl2L_mul_sl2U [CharP F 2] :
    sl2U (1 : F) * sl2L 1 * sl2U 1 = sl2W := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2W, sl2U, sl2L, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem exists_sl2U_sl2L_sl2U (g : SpecialLinearGroup (Fin 2) F) (hc : g 1 0 ≠ 0) :
    ∃ x y : F, g = sl2U x * sl2L (g 1 0) * sl2U y := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  refine ⟨(g 0 0 - 1) / g 1 0, (g 1 1 - 1) / g 1 0, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2U, sl2L, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> first | linear_combination (-1 : F) * hdet | linear_combination hdet | ring

theorem closure_sl2U_sl2W [CharP F 2] :
    Subgroup.closure (Set.range (sl2U (F := F)) ∪ {sl2W}) = ⊤ := by
  set S : Set (SpecialLinearGroup (Fin 2) F) := Set.range (sl2U (F := F)) ∪ {sl2W} with hS
  have hU : ∀ a : F, sl2U a ∈ Subgroup.closure S := fun a =>
    Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have hw : (sl2W : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.closure S :=
    Subgroup.subset_closure (Or.inr rfl)
  have hL : ∀ a : F, sl2L a ∈ Subgroup.closure S := fun a => by
    rw [← sl2W_mul_sl2U_mul_sl2W a]
    exact mul_mem (mul_mem hw (hU a)) hw
  have hc : ∀ g : SpecialLinearGroup (Fin 2) F, g 1 0 ≠ 0 → g ∈ Subgroup.closure S := by
    intro g hg
    obtain ⟨x, y, hxy⟩ := exists_sl2U_sl2L_sl2U g hg
    rw [hxy]
    exact mul_mem (mul_mem (hU x) (hL _)) (hU y)
  refine eq_top_iff.mpr fun g _ => ?_
  by_cases hg : g 1 0 = 0
  · have hdet := g.det_coe
    rw [Matrix.det_fin_two, hg] at hdet
    have hd : g 1 1 ≠ 0 := fun h => by simp [h] at hdet
    have hg' : ((g * sl2L (1 : F) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      simp [sl2L, Matrix.mul_apply, Fin.sum_univ_two, hg, hd]
    have h2 := hc _ hg'
    have : g = (g * sl2L 1) * (sl2L (1 : F))⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem h2 (inv_mem (hL 1))
  · exact hc g hg

end CFSG.Quasithin.S15223
