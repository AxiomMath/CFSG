module

public import CFSG.Sporadic.Presentation.Co3Inputs
public import Certificates.Certificate9105

public section

namespace CFSG.Sporadic.Presentation.Co3

theorem finite_card_le : Finite TauCeti.SporadicName.Co3.Group ∧
    Nat.card TauCeti.SporadicName.Co3.Group ≤ 495766656000 :=
  Certificates.certificate9105

end CFSG.Sporadic.Presentation.Co3
