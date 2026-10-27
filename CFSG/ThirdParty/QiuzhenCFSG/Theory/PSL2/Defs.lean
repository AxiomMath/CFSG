module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Projective special linear group in dimension two

The concrete `PSL(2, K)` matrix-group model, copied from
`GorensteinWalter.Classification.PSL2` and exposed as `Theory.PSL2`.
-/

namespace CFSG.Theory

universe u

/-- `PSL(2, K)`. -/
public abbrev PSL2 (K : Type u) [CommRing K] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) K

end CFSG.Theory
