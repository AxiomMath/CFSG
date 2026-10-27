module

public import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.8.7

The source proves that the norm of a finite extension of finite fields is
surjective.  We record the units-valued form used in Huppert II.10.12.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u v

/-- Huppert II.8.7: the norm on the multiplicative groups of finite fields is
surjective. -/
public theorem huppert_II_8_7_norm_surjective
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] [Finite L] :
    Function.Surjective (Units.map (Algebra.norm K : L →* K)) :=
  FiniteField.unitsMap_norm_surjective K L

end External
end CFSG.BenderSuzuki
