module

public import Certificates.Certificate9126

public section

namespace CFSG.Sporadic.Presentation.McL

theorem card_le :
    Finite TauCeti.SporadicName.McL.Group ∧
      Nat.card TauCeti.SporadicName.McL.Group ≤ 898128000 :=
  Certificates.certificate9126

end CFSG.Sporadic.Presentation.McL
