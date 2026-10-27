module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix

variable {K : Type} [Field K]

@[expose] def blkB (X : Matrix (Fin 3) (Fin 3) K) (u v : K) : Matrix (Fin 5) (Fin 5) K :=
  !![X 0 0, X 0 1, X 0 2, 0, 0;
     X 1 0, X 1 1, X 1 2, 0, 0;
     X 2 0, X 2 1, X 2 2, 0, 0;
     0, 0, 0, u, 0;
     0, 0, 0, 0, v]

theorem blkB_mul (X Y : Matrix (Fin 3) (Fin 3) K) (u v u' v' : K) :
    blkB X u v * blkB Y u' v' = blkB (X * Y) (u * u') (v * v') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkB, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three]

theorem blkB_one : blkB (1 : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB]

theorem blkB_map (σ : K →+* K) (X : Matrix (Fin 3) (Fin 3) K) (u v : K) :
    (blkB X u v).map σ = blkB (X.map σ) (σ u) (σ v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB]

theorem blkB_transpose (X : Matrix (Fin 3) (Fin 3) K) (u v : K) :
    (blkB X u v)ᵀ = blkB Xᵀ u v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB]

theorem blkB_injective {X Y : Matrix (Fin 3) (Fin 3) K} {u v u' v' : K}
    (h : blkB X u v = blkB Y u' v') : X = Y ∧ u = u' ∧ v = v' := by
  refine ⟨?_, by simpa [blkB] using congrFun (congrFun h 3) 3,
    by simpa [blkB] using congrFun (congrFun h 4) 4⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkB] using congrFun (congrFun h 0) 0
  · simpa [blkB] using congrFun (congrFun h 0) 1
  · simpa [blkB] using congrFun (congrFun h 0) 2
  · simpa [blkB] using congrFun (congrFun h 1) 0
  · simpa [blkB] using congrFun (congrFun h 1) 1
  · simpa [blkB] using congrFun (congrFun h 1) 2
  · simpa [blkB] using congrFun (congrFun h 2) 0
  · simpa [blkB] using congrFun (congrFun h 2) 1
  · simpa [blkB] using congrFun (congrFun h 2) 2

theorem det_blkB (X : Matrix (Fin 3) (Fin 3) K) (u v : K) :
    (blkB X u v).det = X.det * u * v := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blkB, Fin.succAbove]
  ring

theorem eq_blkB_of_zero (M : Matrix (Fin 5) (Fin 5) K)
    (h03 : M 0 3 = 0) (h04 : M 0 4 = 0) (h13 : M 1 3 = 0) (h14 : M 1 4 = 0) (h23 : M 2 3 = 0)
    (h24 : M 2 4 = 0) (h30 : M 3 0 = 0) (h31 : M 3 1 = 0) (h32 : M 3 2 = 0) (h34 : M 3 4 = 0)
    (h40 : M 4 0 = 0) (h41 : M 4 1 = 0) (h42 : M 4 2 = 0) (h43 : M 4 3 = 0) :
    M = blkB !![M 0 0, M 0 1, M 0 2; M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2] (M 3 3) (M 4 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB, *]

end CFSG.RankThree.PartOne.KFOUT3
