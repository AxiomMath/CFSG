module

public import CFSG.Certificates.KernelBound
public import Certificates.Certificate9104

public section

namespace CFSG.Sporadic.Presentation.Co2

theorem finite_card_le_fusion :
    Finite TauCeti.SporadicName.Co2.Group ∧
      Nat.card TauCeti.SporadicName.Co2.Group ≤ 42305421312000 :=
  Certificates.certificate9104

end CFSG.Sporadic.Presentation.Co2
