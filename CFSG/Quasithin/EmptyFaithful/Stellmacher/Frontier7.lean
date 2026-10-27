module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss34At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss34At H M :=
  hss34At_of hA (hss28At_of_hss26A hA h26)
    EmptyFaithful.Stellmacher.OrdinaryProofs.irrSecSec
    EmptyFaithful.Stellmacher.OrdinaryProofs.hss15Sec

end F53.Stellmacher

theorem F53.Stellmacher.Hss34_of_hss26A (h26 : F53.Stellmacher.Hss26A) : F53.Stellmacher.Hss34 :=
  fun G _ _ H M S hA => F53.Stellmacher.hss34At_of_hss26A hA (h26 G H M S hA)

end CFSG.Quasithin
