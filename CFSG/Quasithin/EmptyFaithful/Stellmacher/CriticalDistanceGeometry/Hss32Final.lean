module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepDEF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss32DEFAt_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) :
    Hss32DEFAt H M :=
  hss32DEFAt_of hA (hss27At_of_hss26A hA h26) (hss28At_of_hss26A hA h26) (hss113aAt_of hA)
    (hss113cAt_of hA)

theorem hss32At_of_hss26A_only (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss32At H M :=
  hss32At_of_hss26A hA h26 (hss32DEFAt_of_hss26A hA h26)

end F53.Stellmacher

end CFSG.Quasithin
