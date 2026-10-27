module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaWeylAux
public import Mathlib.LinearAlgebra.Matrix.Notation
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.StandardType.NoOffRest
open scoped Matrix CFSG.Decide.Bounded

@[expose] def M6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) (ZMod 3) :=
  !![2, 1, 2, 2, 1, 0; 1, 1, 2, 0, 0, 0; 2, 2, 1, 1, 2, 0; 2, 0, 1, 0, 0, 0;
    1, 0, 2, 0, 1, 0; 0, 0, 0, 0, 0, 0]

@[expose] def f6 (x y : Fin Tag.E6.rank → ZMod 3) : ZMod 3 := x ⬝ᵥ (M6 *ᵥ y)

theorem M6_eq : M6 = E6Dep.coordFᵀ * E6Dep.gram6 * E6Dep.coordF := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem e6ModelForm_eq_f6 (x y : Fin Tag.E6.rank → ZMod 3) : e6ModelForm x y = f6 x y := by
  simp only [e6ModelForm, E6Dep.bil6, f6, M6_eq]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec (A := E6Dep.coordF)]
  exact dotProduct_comm _ _

@[expose] def bX0 : Fin Tag.E6.rank → ZMod 3 := e6ModelBaseTwo

theorem bX0_spec : kDotP 3 bX0 = 0 ∧ f6 bX0 bX0 = 2 := by
  decide +kernel

end CFSG.StandardType.E6QTwo

end
