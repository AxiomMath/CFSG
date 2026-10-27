module

public import Certificates.Certificate9266

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_r4 :
    Finite (PG (2 + 1) (epsRels U T5 ![false, true, false, false, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, true, false, false, false])) ≤ 244823040 :=
  Certificates.certificate9266

end CFSG.Monster.Schur.M24
