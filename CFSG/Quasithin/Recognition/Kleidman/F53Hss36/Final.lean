module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Assembly
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim46
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.IvBound
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.FactH8
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.PerfectH67

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim5Spec : Claim5Spec H M S := fun C => C.claim5

theorem hss36Inputs : Hss36Inputs H M S :=
  ⟨claim4Spec, claim5Spec, claim6Spec, ivBoundSpec, starSpec⟩

theorem factH6 : FactH6 G := fun hQ hQX hXQ => commutator_oTwoRes_oTwoRes hQ hQX hXQ

theorem factH7 : FactH7 := fun Y hY => nat_irred_alt Y hY

theorem hss36NatAt_of_finite (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (h34 : Hss34At H M)
    (hH11 : FactH11) (hH12 : FactH12) : Hss36NatAt H M :=
  hss36NatAt_of_inputs hA h26 h34 hss36Inputs factH6 factH7 factH8 hH11 hH12

end CFSG.Quasithin.Kleidman.F53Hss36
