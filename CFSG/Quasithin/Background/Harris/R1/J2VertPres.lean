module

public import Certificates.Certificate300201

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.CosetTable

theorem card_PG_le (ε : Bool) :
    Finite (PG 8 (vRels ε)) ∧ Nat.card (PG 8 (vRels ε)) ≤ 3840 :=
  Certificates.certificate300201 ε

end CFSG.Quasithin.Background.Harris.R1.J2Vert
