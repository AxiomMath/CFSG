module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Final
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.S5Facts2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26A_Holds
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier7

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53
open CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem factH11 : FactH11 := fun hc hcT _ hτ => fix_point_of_natAct_fix hc hcT hτ

theorem factH12 : FactH12 := fun hP _ hY h4 => le_fixW_of_invariant_card_le_four hP hY h4

theorem hss36NatAt_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h34 : Hss34At H M) :
    Hss36NatAt H M :=
  hss36NatAt_of_finite hA h26 h34 factH11 factH12

theorem hss36Nat_of (h26 : Hss26A) (h34 : Hss34) : F53.Stellmacher.Hss36Nat :=
  fun G _ _ H M S hA => hss36NatAt_of hA (h26 G H M S hA) (h34 G H M S hA)

theorem hss36Nat_holds : F53.Stellmacher.Hss36Nat :=
  hss36Nat_of hss26A_holds (F53.Stellmacher.Hss34_of_hss26A hss26A_holds)

end CFSG.Quasithin.Kleidman.F53Hss36
