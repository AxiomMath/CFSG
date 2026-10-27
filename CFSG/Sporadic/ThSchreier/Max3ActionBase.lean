
module

public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.Sporadic.ThSchreier.Enc8

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped commutatorElement

theorem matrix_ext_mulVec {A B : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v)

end CFSG.Sporadic.ThSchreier
