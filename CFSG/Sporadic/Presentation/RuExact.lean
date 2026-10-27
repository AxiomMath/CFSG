module

public import CFSG.Sporadic.Presentation.RuExactInputs
public import Certificates.Certificate9129

public section

namespace CFSG.Sporadic.Presentation.Ru

theorem finite_card_le : Finite TauCeti.SporadicName.Ru.Group ∧
    Nat.card TauCeti.SporadicName.Ru.Group ≤ 145926144000 :=
  Certificates.certificate9129

end CFSG.Sporadic.Presentation.Ru
