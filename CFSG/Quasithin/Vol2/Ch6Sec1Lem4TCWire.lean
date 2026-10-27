module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFinal
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFF4

public section

namespace CFSG.Quasithin.H13.T614


theorem titsOrderFact_holds
    : TitsOrderFact := fun _ _ h =>
  CFSG.Quasithin.T1521SCut.card_isTits h

theorem res614TitsCore_of_finite
    (hT2 : TitsRankThreeFact) (hT4 : TitsParabolicNormalizerFact)
    (hO2 : L216ModuleFact) (hO3 : L216CoreFact) (hO4 : L216NormalizerFact)
    (hNZV : NZVNormalFact) : Res614TitsCore :=
  res614TitsCore_of titsOrderFact_holds titsBasicFact_holds titsOver5Fact_holds hT2 hT4 hO2 hO3
    hO4 ffCentralizerFact_holds hNZV

end CFSG.Quasithin.H13.T614
