module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def ggPDC3 : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  CartanMatrix.F₄.map (fun z : ℤ => (z : ZMod 3))

@[expose] def ggPDRefl (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (i : Fin 4) :
    Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  1 - Matrix.single i i 1 * M

@[expose] def ggPDChar {K : Type} [Field K] (ζ : K) (x : ZMod 3) : K := ζ ^ x.val

end CFSG.StandardType

end
