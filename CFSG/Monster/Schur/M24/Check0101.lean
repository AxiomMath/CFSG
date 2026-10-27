module

public import Certificates.Certificate9255

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0101 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, true, false, true])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, true, false, true])) ≤ 244823040 :=
  Certificates.certificate9255 c

end CFSG.Monster.Schur.M24
