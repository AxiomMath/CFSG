module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Fix
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Step

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

open S35.II

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem step21 (hS : Sit H M S) (hII : CaseII H M) : Step21 H M :=
  step21_of_fixZ hS hII (fixZ hS)

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
