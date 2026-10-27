module

public import Certificates.Certificate9103
public import CFSG.Sporadic.Presentation.Co2BaseInputs

public section

namespace CFSG.Sporadic.Presentation.Co2

theorem card_le_cover :
    Nat.card TauCeti.SporadicName.Co2.Group ≤ 42305421312000 :=
  Certificates.certificate9103

end CFSG.Sporadic.Presentation.Co2
