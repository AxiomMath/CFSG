module

public import Certificates.Certificate9257

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0111 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, true, true, true])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, true, true, true])) ≤ 244823040 :=
  Certificates.certificate9257 c

end CFSG.Monster.Schur.M24
