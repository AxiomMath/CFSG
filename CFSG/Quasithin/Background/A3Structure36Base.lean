
module

public import CFSG.Quasithin.Background.A3StructureFactsProved

@[expose] public section

namespace CFSG.Quasithin

theorem A36Facts.of_proved (h129 : A129One) (hl2 : L2MultiplierFact) (h3 : ThreeCoverFact)
    (hlist : A23SQTKListFact) (hcat : CatalogStepFact) : A36Facts :=
  { A36CaseBFacts.of_proved h129 hl2 with
    threeCover := h3
    list := hlist
    catalog := hcat }

end CFSG.Quasithin
