module

public import Certificates.Certificate9254

public section

namespace CFSG.Monster.Schur.M24

open CFSG.CosetTable

theorem bound_0100 (c : Bool) :
    Finite (PG (2 + 1) (epsRels U T5 ![false, c, true, false, false])) ∧
      Nat.card (PG (2 + 1) (epsRels U T5 ![false, c, true, false, false])) ≤ 244823040 :=
  Certificates.certificate9254 c

end CFSG.Monster.Schur.M24
