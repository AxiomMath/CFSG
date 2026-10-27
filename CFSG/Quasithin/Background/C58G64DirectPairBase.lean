module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.C58.G64D

open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

variable [Finite V]

private instance pairBase_finite_glv : Finite (GLV V) :=
  Finite.of_injective (fun e : GLV V => (e : V → V)) DFunLike.coe_injective

end CFSG.Quasithin.C58.G64D
