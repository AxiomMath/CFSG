module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.Classical.GL3

open Matrix
open scoped Pointwise commutatorElement

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def frobS : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], !![0, 0, 1; 1, 0, 1; 0, 1, 0] ^ 6, by decide, by decide⟩

@[expose] def frobX : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], !![1, 0, 0; 0, 0, 1; 0, 1, 1] ^ 2, by decide, by decide⟩

theorem frobS_pow_seven : frobS ^ 7 = 1 := Units.ext (by decide)

theorem frobS_ne_one : frobS ≠ 1 := fun h => absurd (congrArg Units.val h) (by decide)

theorem frobX_pow_three : frobX ^ 3 = 1 := Units.ext (by decide)

theorem frobX_ne_one : frobX ≠ 1 := fun h => absurd (congrArg Units.val h) (by decide)

theorem frobX_conj_frobS : frobX * frobS * frobX⁻¹ = frobS ^ 2 := Units.ext (by decide)

end CFSG.RankThree.Classical.GL3
