module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Assembly
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddAssembly
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddSeven
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7DichB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S43.Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss43OddAt_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss43OddAt H M :=
  fun _ hs ho => false_of_odd hA h26 hs ho (gap7At H M) (oddEndAt H M)

end F53.Stellmacher.S43.Odd

theorem F53.Stellmacher.S43.Odd.hss43Odd_of (h26 : F53.Stellmacher.Hss26A) :
    F53.Stellmacher.Hss43Odd :=
  fun _ _ _ H M _ hA => F53.Stellmacher.S43.Odd.hss43OddAt_of hA (h26 _ H M _ hA)

theorem F53.Stellmacher.S43.Odd.hss43_of (h26 : F53.Stellmacher.Hss26A) :
    F53.Stellmacher.Hss43 :=
  F53.Stellmacher.Hss43_of_odd h26 (F53.Stellmacher.S43.Odd.hss43Odd_of h26)

end CFSG.Quasithin
