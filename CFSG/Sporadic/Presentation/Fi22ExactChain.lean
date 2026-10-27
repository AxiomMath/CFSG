module

public import Certificates.Certificate9107

public section

namespace CFSG.Sporadic.Presentation.Fi22Exact

open CFSG.CosetTable

theorem card_F_le :
    Finite (PG 6 wsF) ∧ Nat.card (PG 6 wsF) ≤ 774741019852800 :=
  Certificates.certificate9107.1

theorem card_presented_Fi22_le :
    Finite TauCeti.SporadicName.Fi22.Group ∧
      Nat.card TauCeti.SporadicName.Fi22.Group ≤ 64561751654400 :=
  Certificates.certificate9107.2

end CFSG.Sporadic.Presentation.Fi22Exact
