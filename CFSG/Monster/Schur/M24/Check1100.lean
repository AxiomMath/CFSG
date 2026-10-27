module

public import Certificates.Certificate9262

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1100 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, true, false, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, true, false, false])) ≤ 244823040 :=
  Certificates.certificate9262 c

end CFSG.Monster.Schur.M24
