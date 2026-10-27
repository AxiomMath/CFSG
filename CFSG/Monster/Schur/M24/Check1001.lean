module

public import Certificates.Certificate9259

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1001 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, false, false, true])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, false, false, true])) ≤ 244823040 :=
  Certificates.certificate9259 c

end CFSG.Monster.Schur.M24
