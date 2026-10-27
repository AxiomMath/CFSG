module

public import Certificates.Certificate9258

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1000 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, false, false, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, false, false, false])) ≤ 244823040 :=
  Certificates.certificate9258 c

end CFSG.Monster.Schur.M24
