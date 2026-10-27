module

public import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def sl2UnipU (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] def sl2UnipV (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem coe_sl2UnipU (F : Type) [Field F] :
    ((sl2UnipU F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] := rfl

theorem coe_sl2UnipV (F : Type) [Field F] :
    ((sl2UnipV F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; 1, 1] := rfl

theorem sl2UnipU_ne_one (F : Type) [Field F] : sl2UnipU F ≠ 1 := by
  intro h
  have H := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_sl2UnipU] at H

theorem sl2UnipV_ne_one (F : Type) [Field F] : sl2UnipV F ≠ 1 := by
  intro h
  have H := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp [coe_sl2UnipV] at H

theorem sl2UnipU_ne_sl2UnipV (F : Type) [Field F] : sl2UnipU F ≠ sl2UnipV F := by
  intro h
  have H := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_sl2UnipU, coe_sl2UnipV] at H

theorem sl2UnipU_mul_self (F : Type) [Field F] [CharP F 2] :
    sl2UnipU F * sl2UnipU F = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2UnipU, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

theorem sl2UnipV_mul_self (F : Type) [Field F] [CharP F 2] :
    sl2UnipV F * sl2UnipV F = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2UnipV, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

theorem exists_two_involutions_projSL_field (F : Type) [Field F] [CharP F 2] :
    ∃ u v : projSL 2 F, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 := by
  refine ⟨(projSLTwoEquivSL F).symm (sl2UnipU F), (projSLTwoEquivSL F).symm (sl2UnipV F),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [ne_eq, MulEquiv.map_eq_one_iff]
    exact sl2UnipU_ne_one F
  · rw [ne_eq, MulEquiv.map_eq_one_iff]
    exact sl2UnipV_ne_one F
  · exact (projSLTwoEquivSL F).symm.injective.ne (sl2UnipU_ne_sl2UnipV F)
  · rw [← map_mul, sl2UnipU_mul_self F, map_one]
  · rw [← map_mul, sl2UnipV_mul_self F, map_one]

theorem exists_two_involutions_projSL (m : ℕ) (hm : 1 ≤ m) :
    ∃ u v : projSL 2 (GaloisField 2 m), u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 := by
  exact exists_two_involutions_projSL_field (GaloisField 2 m)

end CFSG.RankThree.PartTwo.Sec21.Hering233i
