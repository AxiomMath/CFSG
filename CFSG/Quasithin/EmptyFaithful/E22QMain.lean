module

public import CFSG.Quasithin.EmptyFaithful.E22QPlumb
public import CFSG.Quasithin.EmptyFaithful.E22QStar

public section

namespace CFSG.Quasithin.E2.E22N

theorem e22NParamW_of_orb
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h114 : E114OneResRest) :
    E2.E22NParamW :=
  e22NParamW_of_wrCore hOrb wrCore h114

end CFSG.Quasithin.E2.E22N
