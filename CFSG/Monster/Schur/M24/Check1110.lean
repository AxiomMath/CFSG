module

public import Certificates.Certificate9264

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1110 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, true, true, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, true, true, false])) ≤ 244823040 :=
  Certificates.certificate9264 c

end CFSG.Monster.Schur.M24
