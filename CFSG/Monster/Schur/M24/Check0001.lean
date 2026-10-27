module

public import Certificates.Certificate9251

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0001 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, false, false, true])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, false, false, true])) ≤ 244823040 :=
  Certificates.certificate9251 c

end CFSG.Monster.Schur.M24
