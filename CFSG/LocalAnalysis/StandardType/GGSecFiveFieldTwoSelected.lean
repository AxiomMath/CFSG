module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcMember

public section

namespace CFSG.StandardType

namespace FieldTwoSelected

theorem ggSecFiveQTwoFieldTwoSelectedInput_of_twistedE6
    (hTw : GGSecFiveQTwoFieldTwoSelectedAt .twistedE6) :
    GGSecFiveQTwoFieldTwoSelectedInput :=
  FieldTwoPOmega.ggSecFiveQTwoFieldTwoSelectedInput_of_exc_tags
    FieldTwoF4.ggSecFiveQTwoFieldTwoSelectedAt_F4 FieldTwoE6.ggSecFiveQTwoFieldTwoSelectedAt_E6
    (FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_exc_of_noncentral (.inr (.inr (.inl rfl)))
      FieldTwoExc.exists_selectedSL2Model_E7
      (FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_noncentral_of_core (Or.inl rfl)))
    (FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_exc_of_noncentral (.inr (.inr (.inr rfl)))
      FieldTwoE8.exists_selectedSL2Model_E8
      (FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_noncentral_of_core (Or.inr rfl))) hTw

end FieldTwoSelected

end CFSG.StandardType

end
