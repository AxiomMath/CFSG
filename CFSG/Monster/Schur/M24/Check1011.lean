module

public import Certificates.Certificate9261

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1011 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, false, true, true])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, false, true, true])) ≤ 244823040 :=
  Certificates.certificate9261 c

end CFSG.Monster.Schur.M24
