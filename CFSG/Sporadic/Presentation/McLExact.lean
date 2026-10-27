module

public import CFSG.Sporadic.Bridge.McLSurj
public import Certificates.Certificate9125

public section

namespace CFSG.Sporadic.Presentation.McL

theorem finite_card_le :
    Finite TauCeti.SporadicName.McL.Group ∧
    Nat.card TauCeti.SporadicName.McL.Group ≤ 898128000 :=
  Certificates.certificate9125

end CFSG.Sporadic.Presentation.McL

namespace CFSG.Sporadic.Bridge.McL

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.McL ≃* TauCeti.SporadicName.McL.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.McL.finite_card_le.1
    Presentation.McL.finite_card_le.2

end CFSG.Sporadic.Bridge.McL
