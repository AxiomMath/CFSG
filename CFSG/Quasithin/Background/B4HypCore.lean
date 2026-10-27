module

public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def B4HypCore {V : Type} [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)) : Prop :=
  L = quasithinGenFitting G ∧ CFSG.IsQuasisimple ↥L ∧ XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤

theorem B4Hyp.core {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (h : B4Hyp G L) : B4HypCore G L :=
  h.2

end CFSG.Quasithin
