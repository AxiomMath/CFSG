module

public import CFSG.Quasithin.Vol2.Ch10SecA312AF
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.QuasithinUnique

theorem evenLieAutInner_proved
    : Ch1.EvenLieAutInner :=
  Ch1.evenLieAutInner_of_tits K1.titsSylowCentralizingAutInner

theorem sporadicAutInner_proved
    : Ch1.SporadicAutInner :=
  Ch1.sporadicAutInner_of_residual
    (Ch1.sporadicResidualAutInner_of_J4 (Ch1.j4AutInner_of_outOdd Setup.X1.j4OuterOdd))

theorem a312AutCent_of_zcent
    (hList : Vol2Native.A312ListFactsCat) (hZ : A312ZCentFacts) : A312AutCent :=
  a312AutCent_of hList evenLieAutInner_proved sporadicAutInner_proved hZ

end CFSG.Quasithin.Vol2.Ch10.A312A
