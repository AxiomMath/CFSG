module

public import CFSG.Sporadic.Presentation.Co2
public import CFSG.Sporadic.Bridge.Co2Surj

public section

namespace CFSG.Sporadic.Bridge.Co2

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Co2 ≃* TauCeti.SporadicName.Co2.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Co2.finite_card_le.1
    Presentation.Co2.finite_card_le.2

end CFSG.Sporadic.Bridge.Co2
