module

public import Certificates.Certificate9101

public section

namespace CFSG.Sporadic.Presentation.Co2

theorem finite_card_le : Finite TauCeti.SporadicName.Co2.Group ∧
    Nat.card TauCeti.SporadicName.Co2.Group ≤ 42305421312000 :=
  Certificates.certificate9101

theorem finite : Finite TauCeti.SporadicName.Co2.Group :=
  Certificates.certificate9101.1

end CFSG.Sporadic.Presentation.Co2
