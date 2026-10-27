module

public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.StandardType

section Lattice

variable {m : ℕ}

@[expose] def ggLatCartan (Q : Matrix (Fin m) (Fin m) ℤ) (v w : Fin m → ℤ) : ℤ :=
  2 * dotProduct v (Q.mulVec w) / dotProduct w (Q.mulVec w)

@[expose] def ggLatRefl (Q : Matrix (Fin m) (Fin m) ℤ) (w y : Fin m → ℤ) : Fin m → ℤ :=
  y - ggLatCartan Q y w • w

@[expose] def GGLatForm (Q : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  Q.transpose = Q ∧ ∀ y : Fin m → ℤ, y ≠ 0 → 0 < dotProduct y (Q.mulVec y)

@[expose] def GGLatRoot (Q : Matrix (Fin m) (Fin m) ℤ) (w : Fin m → ℤ) : Prop :=
  w ≠ 0 ∧ ∀ y : Fin m → ℤ, dotProduct w (Q.mulVec w) ∣ 2 * dotProduct y (Q.mulVec w)

end Lattice

end CFSG.StandardType
