module

public import Certificates.Certificate9130

public section

namespace CFSG.Sporadic.Presentation.Suz

theorem finite_card_le : Finite TauCeti.SporadicName.Suz.Group ∧
    Nat.card TauCeti.SporadicName.Suz.Group ≤ 448345497600 :=
  Certificates.certificate9130.1

end CFSG.Sporadic.Presentation.Suz
