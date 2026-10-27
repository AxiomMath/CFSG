module

public import Certificates.Certificate9260

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_1010 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![true, c, false, true, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![true, c, false, true, false])) ≤ 244823040 :=
  Certificates.certificate9260 c

end CFSG.Monster.Schur.M24
