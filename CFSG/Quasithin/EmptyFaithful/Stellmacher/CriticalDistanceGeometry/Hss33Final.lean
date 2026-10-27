module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Hss32Final
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Final

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss33At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss33At H M :=
  hss33At_of hA (hss32At_of_hss26A_only hA h26) (hss113aAt_of hA) noA5Transvection_holds
    (hss33Step3At_of hA (hss28At_of_hss26A hA h26) (hss113aAt_of hA))

end F53.Stellmacher

theorem F53.Stellmacher.Hss33_of_hss26A (h26 : F53.Stellmacher.Hss26A) : F53.Stellmacher.Hss33 :=
  fun G _ _ H M S hA => F53.Stellmacher.hss33At_of_hss26A hA (h26 G H M S hA)

end CFSG.Quasithin
