module

public import CFSG.Sporadic.Presentation.HNInputs
public import Certificates.Certificate9114

public section

namespace CFSG.Sporadic.Presentation.HN

theorem finite_card_le : Finite TauCeti.SporadicName.HN.Group ∧
    Nat.card TauCeti.SporadicName.HN.Group ≤ 273030912000000 :=
  Certificates.certificate9114

end CFSG.Sporadic.Presentation.HN
