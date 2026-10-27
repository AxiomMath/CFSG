module

public import Certificates.Data.J3Sylow

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure CommTripleData where
  base : SylowCentralData
  trip : List (Nat × Nat × Nat)

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def commTripleOK [Inhabited M] (D : SylowCentralData) (R E : Array M)
    (t : Nat × Nat × Nat) : Bool :=
  decide (t.1 < D.nregs) && decide (t.2.1 < D.nregs) && decide (t.2.2 < D.nregs) &&
    (t.2.2 == D.rk1 || t.2.2 == D.rk2) && O.memOK E R[t.2.1]! &&
    O.eq (O.pow R[t.1]! 3) O.one &&
    O.eq (O.mul R[t.1]! (O.mul R[t.2.2]! R[t.2.1]!)) (O.mul R[t.2.1]! R[t.2.2]!)

@[expose] def commTripleFacts [Inhabited M] [Inhabited V] (D : CommTripleData) (R E : Array M) :
    Bool :=
  decide (9 < D.trip.length) && D.trip.all (O.commTripleOK D.base R E) &&
    O.distinctOK (D.trip.toArray.map fun t => O.vmul (O.unit D.base.t) R[t.1]!)

@[expose] def commTripleCheck [Inhabited M] [Inhabited V] (D : CommTripleData) : Bool :=
  let R := O.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog
  let En := O.enumBFS #[R[D.base.rk1]!, R[D.base.rk2]!] D.base.nP
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) && D.base.regsLt &&
    O.sylowGenFacts D.base R[D.base.rk1]! R[D.base.rk2]! &&
    O.enumOK #[R[D.base.rk1]!, R[D.base.rk2]!] D.base.nP D.base.t En.1 En.2.1 En.2.2.1 En.2.2.2 &&
    O.commTripleFacts D R En.1

end Ops

@[expose] def j3CommTripleData : CommTripleData where
  base := { j3SylowCentralData with
    nregs := 77
    prog := j3SylowCentralData.prog ++ [
      .pow 2 23 29, .pow 7 23 30, .pow 8 23 31, .pow 2 26 32, .pow 7 26 33, .pow 8 26 34,
      .mul 23 26 35, .mul 35 31 36, .mul 36 34 37, .mul 29 26 38, .mul 38 30 39, .mul 39 34 40,
      .mul 26 23 41, .mul 41 34 42, .mul 42 31 43, .mul 32 23 44, .mul 44 33 45, .mul 45 31 46,
      .mul 26 23 47, .mul 31 34 48, .mul 47 26 49, .mul 49 48 50, .mul 50 34 51,
      .mul 26 29 52, .mul 30 34 53, .mul 52 26 54, .mul 54 53 55, .mul 55 34 56,
      .mul 32 29 57, .mul 30 33 58, .mul 57 26 59, .mul 59 58 60, .mul 60 34 61,
      .mul 23 26 62, .mul 34 31 63, .mul 62 23 64, .mul 64 63 65, .mul 65 31 66,
      .mul 23 32 67, .mul 33 31 68, .mul 67 23 69, .mul 69 68 70, .mul 70 31 71,
      .mul 29 32 72, .mul 33 30 73, .mul 72 23 74, .mul 74 73 75, .mul 75 31 76] }
  trip := [(37, 23, 26), (40, 29, 26), (43, 26, 23), (46, 32, 23), (51, 47, 26), (56, 52, 26),
    (61, 57, 26), (66, 62, 23), (71, 67, 23), (76, 72, 23)]

end CFSG.SectionRank.Native
