module

public import Certificates.Certificate9256

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0110 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, true, true, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, true, true, false])) ≤ 244823040 :=
  Certificates.certificate9256 c

end CFSG.Monster.Schur.M24
