module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType

@[expose] def ggCoxeterMatrixD (n : ℕ) : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j => if i = j then 1 else if CartanMatrix.D n i j = 0 then 2 else 3
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, (CartanMatrix.D_isSymm n).apply j i,
      eq_comm (a := j)]
  diagonal i := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ite_false]
    split_ifs <;> omega

theorem ggCoxeterMatrixD_apply (n : ℕ) (i j : Fin n) :
    ggCoxeterMatrixD n i j =
      if i = j then 1 else if CartanMatrix.D n i j = 0 then 2 else 3 := rfl

end CFSG.StandardType
