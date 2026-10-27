module

public import CFSG.Quasithin.Background.A3FactsSchreierNative
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.J4SCatalog

public section

namespace CFSG.Quasithin.A3Facts

open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase
  sporadicSchreierCase_of_outer)

theorem sporadicSchreierCase_J4_native
    : SporadicSchreierCase .J4 :=
  sporadicSchreierCase_of_outer CFSG.Sporadic.J4Schreier.outer_J4_isSolvable

theorem sporadicSchreierCase_He_native
    : SporadicSchreierCase .He :=
  sporadicSchreierCase_of_outer CFSG.Sporadic.Schreier.AT_He_Schreier.2.2

theorem schreierSQTK
    : SchreierSQTK :=
  schreierSQTK_of_J4_He sporadicSchreierCase_J4_native sporadicSchreierCase_He_native

end CFSG.Quasithin.A3Facts
