module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev fStarMod (H : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  CFSG.generalizedFitting (↥H ⧸ CFSG.pCore 2 ↥H)

@[expose] def fStarPre (H : Subgroup G) : Subgroup G :=
  ((fStarMod H).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

end CFSG.Quasithin.RonanE42
