module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin

namespace SBc17

abbrev SL2 (F : Type) [Field F] : Type := Matrix.SpecialLinearGroup (Fin 2) F

variable {F : Type} [Field F]

@[expose] def uElt (x : F) : SL2 F := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def lElt (x : F) : SL2 F := ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def tElt (a : Fˣ) : SL2 F :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

@[expose] def wElt : SL2 F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def borelSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg]

@[expose] def upperSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg]

@[expose] def torusSub (F : Type) [Field F] : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg]

theorem uElt_mul (x y : F) : uElt x * uElt y = uElt (x + y) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uElt, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uElt_zero : uElt (0 : F) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [uElt]

theorem mem_upperSub_iff {g : SL2 F} : g ∈ upperSub F ↔ ∃ x : F, g = uElt x := by
  constructor
  · rintro ⟨h00, h11, h10⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [uElt, h00, h11, h10]
  · rintro ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [uElt]

theorem mem_borelSub_iff {g : SL2 F} :
    g ∈ borelSub F ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem upperSub_le_borelSub : upperSub F ≤ borelSub F := fun _ h => h.2.2

theorem torusSub_le_borelSub : torusSub F ≤ borelSub F := fun _ h => h.2

end SBc17

end CFSG.Quasithin
