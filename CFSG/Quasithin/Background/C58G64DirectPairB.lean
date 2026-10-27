module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.C58.G64D

open CFSG.QuasithinUnique CFSG.Quasithin.G11

instance instFiniteGLVPairB {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (GLV V) :=
  Finite.of_injective (fun g : GLV V => (g : V → V)) (fun a b h => LinearEquiv.ext (congrFun h))

end CFSG.Quasithin.C58.G64D
