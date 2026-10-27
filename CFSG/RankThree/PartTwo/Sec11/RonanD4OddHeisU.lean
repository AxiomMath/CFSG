module

public import CFSG.RankThree.PartTwo.Sec11.RonanD4OddHeisDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open scoped MatrixGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {F : Type} [Field F]

theorem stdUnitary_heisX (σ : F →+* F) (ω : F) (hω : ω ^ 3 = 1) (hσ : σ ω = ω⁻¹) :
    stdUnitary σ (heisX ω hω) = heisX ω hω := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hX : ((heisX ω hω : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![1, ω, ω ^ 2] := rfl
  have hmap : (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) F).map σ =
      Matrix.diagonal ![1, ω⁻¹, (ω ^ 2)⁻¹] := by
    rw [Matrix.diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hσ]
  have hinv : (Matrix.diagonal ![1, ω⁻¹, (ω ^ 2)⁻¹] : Matrix (Fin 3) (Fin 3) F)⁻¹ =
      Matrix.diagonal ![1, ω, ω ^ 2] := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hω0]
  apply Subtype.ext
  rw [coe_stdUnitary, hX, hmap, hinv, Matrix.diagonal_transpose]

theorem stdUnitary_heisY (σ : F →+* F) : stdUnitary σ (heisY : SL(3, F)) = heisY := by
  have hY : ((heisY : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl
  have hmap : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).map σ =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hinv : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F)⁻¹ =
      (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).transpose := by
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  apply Subtype.ext
  rw [coe_stdUnitary, hY, hmap, hinv, Matrix.transpose_transpose]

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
