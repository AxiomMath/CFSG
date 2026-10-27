module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.CertU33PresInputs
public import Certificates.Certificate8081

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

theorem u33Pres_finite_card_le :
    Finite (PG 5 u33PresRels) ∧ Nat.card (PG 5 u33PresRels) ≤ 6048 :=
  Certificates.certificate8081

end CFSG.Quasithin
