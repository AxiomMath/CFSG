module

public import CFSG.Quasithin.H13.NQCatKG68Holds
public import CFSG.Sporadic.Schreier.TitsQTInner
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.QuasithinUnique CFSG.Quasithin

theorem evenLieAutInner_holds :
    Ch1.EvenLieAutInner :=
  Ch1.evenLieAutInner_of_tits fun X _ _ h =>
    CFSG.Sporadic.Schreier.TitsQT.tits_model_sylowCentralizingAutInner X h

theorem u33AutInner_holds : U33AutInner := fun _ _ _ hm β hβ hP =>
  Ch1.oddAutInner_psu3 Nat.prime_three (by decide) hm β hβ hP

theorem e68ComponentFactsLie_holds :
    E6.E68ComponentFactsLie :=
  e68ComponentFactsLie_of_inner evenLieAutInner_holds u33AutInner_holds

theorem e68ComponentFactsCover_holds :
    E6.E68ComponentFactsCover :=
  e68ComponentFactsCover_of_inner evenLieAutInner_holds

end CFSG.Quasithin.H13.KG68
