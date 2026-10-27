module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.StandardType.OrthF3

@[expose] def PolarNondeg3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) : Prop :=
  (QuadraticMap.polarBilin Q).Nondegenerate

end CFSG.StandardType.OrthF3

end
