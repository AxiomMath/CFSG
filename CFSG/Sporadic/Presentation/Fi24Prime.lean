module

public import CFSG.Sporadic.Presentation.Fi24PrimeInputs
public import Certificates.Certificate9112

public section

namespace CFSG.Sporadic.Presentation.Fi24Prime

theorem finite_card_le :
    Finite TauCeti.SporadicName.Fi24Prime.Group ∧
    Nat.card TauCeti.SporadicName.Fi24Prime.Group ≤ 7531234255143970327756800 :=
  ⟨Certificates.certificate9112.1, Certificates.certificate9112.2.trans (by norm_num)⟩

end CFSG.Sporadic.Presentation.Fi24Prime
