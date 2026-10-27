module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def leviLowMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

@[expose] def leviHighMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem leviLowMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    leviLowMat (A * B) = leviLowMat A * leviLowMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviLowMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem leviHighMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    leviHighMat (A * B) = leviHighMat A * leviHighMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviHighMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem leviLowMat_one : leviLowMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviLowMat]

theorem leviHighMat_one : leviHighMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviHighMat]

theorem det_leviLowMat (A : Matrix (Fin 2) (Fin 2) K) : (leviLowMat A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [leviLowMat]

theorem det_leviHighMat (A : Matrix (Fin 2) (Fin 2) K) : (leviHighMat A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [leviHighMat]

@[expose] def leviLow : SL(2, K) →* SL(3, K) where
  toFun A := ⟨leviLowMat (A : Matrix (Fin 2) (Fin 2) K), by rw [det_leviLowMat, A.2]⟩
  map_one' := Subtype.ext (by
    change leviLowMat ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, leviLowMat_one])
  map_mul' A B := Subtype.ext (by
    change leviLowMat ((A * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      leviLowMat (A : Matrix (Fin 2) (Fin 2) K) * leviLowMat (B : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, leviLowMat_mul])

@[expose] def leviHigh : SL(2, K) →* SL(3, K) where
  toFun A := ⟨leviHighMat (A : Matrix (Fin 2) (Fin 2) K), by rw [det_leviHighMat, A.2]⟩
  map_one' := Subtype.ext (by
    change leviHighMat ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, leviHighMat_one])
  map_mul' A B := Subtype.ext (by
    change leviHighMat ((A * B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      leviHighMat (A : Matrix (Fin 2) (Fin 2) K) * leviHighMat (B : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, leviHighMat_mul])

theorem coe_leviLow (A : SL(2, K)) :
    ((leviLow A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      leviLowMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_leviHigh (A : SL(2, K)) :
    ((leviHigh A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      leviHighMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem leviLow_injective : Function.Injective (leviLow : SL(2, K) →* SL(3, K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h := congrArg (fun x : SL(3, K) => (x : Matrix (Fin 3) (Fin 3) K)) hA
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [coe_leviLow, leviLowMat] using this

theorem leviHigh_injective : Function.Injective (leviHigh : SL(2, K) →* SL(3, K)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h := congrArg (fun x : SL(3, K) => (x : Matrix (Fin 3) (Fin 3) K)) hA
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have := congrFun (congrFun h (Fin.succ i)) (Fin.succ j)
  fin_cases i <;> fin_cases j <;> simpa [coe_leviHigh, leviHighMat] using this

theorem leviLow_transvection_zero_one (c : K) :
    leviLow (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  change leviLowMat (1 + Matrix.single 0 1 c) = 1 + Matrix.single 0 1 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviLowMat]

theorem leviLow_transvection_one_zero (c : K) :
    leviLow (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  apply Subtype.ext
  change leviLowMat (1 + Matrix.single 1 0 c) = 1 + Matrix.single 1 0 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviLowMat]

theorem leviHigh_transvection_zero_one (c : K) :
    leviHigh (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  apply Subtype.ext
  change leviHighMat (1 + Matrix.single 0 1 c) = 1 + Matrix.single 1 2 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviHighMat]

theorem leviHigh_transvection_one_zero (c : K) :
    leviHigh (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  change leviHighMat (1 + Matrix.single 1 0 c) = 1 + Matrix.single 2 1 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviHighMat]

theorem reflection_one_conj (c : K) :
    reflection 3 K 1 (by norm_num) (by norm_num) *
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (-c) *
      (reflection 3 K 1 (by norm_num) (by norm_num))⁻¹ =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change reflectionMatrix 3 K 1 * (1 + Matrix.single 0 1 (-c)) =
    (1 + Matrix.single 1 0 c) * reflectionMatrix 3 K 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply,
      Fin.sum_univ_three]

theorem reflection_two_conj (c : K) :
    reflection 3 K 2 (by norm_num) (by norm_num) *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (-c) *
      (reflection 3 K 2 (by norm_num) (by norm_num))⁻¹ =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change reflectionMatrix 3 K 2 * (1 + Matrix.single 1 2 (-c)) =
    (1 + Matrix.single 2 1 c) * reflectionMatrix 3 K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply,
      Fin.sum_univ_three]

end CFSG.Quasithin.H13.NQCore.L3Odd
