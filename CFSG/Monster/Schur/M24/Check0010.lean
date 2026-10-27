module

public import Certificates.Certificate9252

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0010 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, false, true, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, false, true, false])) ≤ 244823040 :=
  Certificates.certificate9252 c

end CFSG.Monster.Schur.M24
