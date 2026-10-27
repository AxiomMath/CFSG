module

public import CFSG.YGroups.Y433.Bound
public import CFSG.Sporadic.Bridge.BPresentation

public section

namespace CFSG.Sporadic.Presentation.B

theorem finite_card_le :
    Finite TauCeti.SporadicName.B.Group ∧
    Nat.card TauCeti.SporadicName.B.Group ≤ 4154781481226426191177580544000000 :=
  Bridge.B.finite_card_le_of_B433 YGroups.B433_finite_card_le.1 YGroups.B433_finite_card_le.2

end CFSG.Sporadic.Presentation.B
