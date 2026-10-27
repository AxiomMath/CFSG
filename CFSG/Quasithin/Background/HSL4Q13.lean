module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.H.Q13

open Matrix

@[expose] def q13 (a b c d e : ZMod 2) (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a, b, c; 0, m 0 0, m 0 1, d; 0, m 1 0, m 1 1, e; 0, 0, 0, 1]

@[expose] def om : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

@[expose] def y0 : Matrix (Fin 4) (Fin 4) (ZMod 2) := q13 0 0 0 0 0 om

@[expose] def tv : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![q13 1 0 0 0 0 1, q13 0 1 0 0 0 1, q13 0 0 0 1 0 1, q13 0 0 0 0 1 1]

@[expose] def sc (k : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) := tv k * y0 * tv k * (y0 * y0)

@[expose] def sci (k : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) := y0 * tv k * (y0 * y0) * tv k

theorem y0_cube : y0 * y0 * y0 = 1 := by decide

theorem tv_sq (k : Fin 4) : tv k * tv k = 1 := by
  revert k
  decide +kernel

theorem sc_mul_sci (k : Fin 4) : sc k * sci k = 1 := by
  revert k
  decide +kernel

@[expose] def cj (a b d e : ZMod 2) (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  q13 (a * m 0 0 + b * m 1 0) (a * m 0 1 + b * m 1 1) 0 (m 0 0 * d + m 0 1 * e)
    (m 1 0 * d + m 1 1 * e) 1

theorem conj_q13 : ∀ m ∈ ({om, om * om} : Finset (Matrix (Fin 2) (Fin 2) (ZMod 2))),
    ∀ a b c d e : ZMod 2, q13 a b c d e m * q13 a b c d e m * q13 a b c d e m = 1 →
      cj a b d e m * q13 a b c d e m = q13 0 0 0 0 0 m * cj a b d e m := by
  decide +kernel

theorem q13_om : q13 0 0 0 0 0 om = y0 := rfl

theorem q13_om_sq : q13 0 0 0 0 0 (om * om) = y0 * y0 := by decide +kernel

end CFSG.Quasithin.H.Q13
