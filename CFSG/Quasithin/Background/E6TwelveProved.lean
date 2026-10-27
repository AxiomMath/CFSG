module

public import CFSG.Quasithin.Background.E6Twelve
public import CFSG.Quasithin.Background.E6ElevenComp
public import CFSG.Quasithin.EmptyFaithful.List115Native

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

theorem e611ComponentCase_proved
    (hE68 : E68ComponentFacts) : E611ComponentCase :=
  e611ComponentCase_of hE68 lemma115_3_List_native

variable {G : Type} [Group G] [Finite G]

theorem as_E_6_12_proved
    (hE68 : E68ComponentFacts) : ASInputs.AS_E_6_12 :=
  as_E_6_12_of (e611ComponentCase_proved hE68)

theorem ch6InE612_proved
    (hE68 : E68ComponentFacts) : H13.Ch6InE612 :=
  ch6InE612_of (e611ComponentCase_proved hE68)

end E6
end CFSG.Quasithin
