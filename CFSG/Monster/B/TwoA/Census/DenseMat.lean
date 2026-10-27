module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Defs

public section

namespace CFSG.Monster.B.TwoA.Census

@[expose] def toMat (a : Array (Array ℚ)) : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.of fun i j => (a[(i : ℕ)]!)[(j : ℕ)]!

@[expose] def ofMat (M : Matrix (Fin 24) (Fin 24) ℚ) : Array (Array ℚ) :=
  ((List.finRange 24).map fun i => ((List.finRange 24).map fun j => M i j).toArray).toArray

@[expose] def mulArr (a b : Array (Array ℚ)) : Array (Array ℚ) :=
  ((List.finRange 24).map fun i : Fin 24 => ((List.finRange 24).map fun k : Fin 24 =>
    ∑ j : Fin 24, (a[(i : ℕ)]!)[(j : ℕ)]! * (b[(j : ℕ)]!)[(k : ℕ)]!).toArray).toArray

theorem getElem!_finRange_map {α : Type*} [Inhabited α] (f : Fin 24 → α) (i : Fin 24) :
    ((List.finRange 24).map f).toArray[(i : ℕ)]! = f i := by
  rw [getElem!_pos _ _ (by simp), List.getElem_toArray, List.getElem_map, List.getElem_finRange]
  rfl

theorem toMat_ofMat (M : Matrix (Fin 24) (Fin 24) ℚ) : toMat (ofMat M) = M := by
  ext i j
  rw [toMat, ofMat, Matrix.of_apply, getElem!_finRange_map, getElem!_finRange_map]

theorem toMat_mulArr (a b : Array (Array ℚ)) : toMat (mulArr a b) = toMat a * toMat b := by
  ext i k
  rw [toMat, mulArr, Matrix.of_apply, getElem!_finRange_map, getElem!_finRange_map,
    Matrix.mul_apply]
  rfl

end CFSG.Monster.B.TwoA.Census
