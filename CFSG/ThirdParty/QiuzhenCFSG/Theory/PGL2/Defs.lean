module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace CFSG
end CFSG
open CFSG

/-!
# Projective general linear group in dimension two

The concrete `PGL(2, K)` matrix-group model, copied from
`GorensteinWalter.Classification.PGL2` and exposed as `Theory.PGL2`.
-/

namespace CFSG.Theory

universe u

/-- `PGL(2, K)`. -/
public abbrev PGL2 (K : Type u) [CommRing K] :=
  Matrix.ProjGenLinGroup (Fin 2) K

end CFSG.Theory
