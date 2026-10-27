module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.StandardType.N2Plane

abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 5)

abbrev Vec := Fin 2 → ZMod 5

@[expose] def e0 : Vec := ![1, 0]

@[expose] def e1 : Vec := ![0, 1]

@[expose] def om : Vec := ![1, 4]

@[expose] def bad2 : Vec := ![1, 2]

@[expose] def bad3 : Vec := ![1, 3]

@[expose] def AxisToDiagonal (M : Mat) : Prop :=
  ∃ i : Fin 2, ∃ eps : ZMod 5, (eps = 1 ∨ eps = 4) ∧
    ∃ c : ZMod 5, c ≠ 0 ∧ M.mulVec (Pi.single i 1) = c • ![1, eps]

instance instDecidableAxisToDiagonal (M : Mat) : Decidable (AxisToDiagonal M) :=
  inferInstanceAs (Decidable (∃ i : Fin 2, ∃ eps : ZMod 5, (eps = 1 ∨ eps = 4) ∧
    ∃ c : ZMod 5, c ≠ 0 ∧ M.mulVec (Pi.single i 1) = c • ![1, eps]))

theorem bad_reflection_dichotomy : ∀ M : Mat,
    M * M = 1 → M ≠ 1 →
    (M.mulVec bad2 = bad2 ∨ M.mulVec bad3 = bad3) →
    AxisToDiagonal M ∨ M = !![0, 3; 2, 0] ∨ M = !![0, 2; 3, 0] := by
  decide +kernel

end CFSG.StandardType.N2Plane

end
