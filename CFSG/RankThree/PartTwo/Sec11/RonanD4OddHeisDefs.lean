module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.RankThree.PartTwo.Sec11.RonanD4Odd

open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def heisX (ω : F) (hω : ω ^ 3 = 1) : SL(3, F) :=
  ⟨Matrix.diagonal ![1, ω, ω ^ 2], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [one_mul, ← pow_succ']
    exact hω⟩

@[expose] def heisY : SL(3, F) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [Matrix.det_fin_three]
    simp⟩

end CFSG.RankThree.PartTwo.Sec11.RonanD4Odd
