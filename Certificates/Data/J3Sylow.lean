module

public import Certificates.Data.CFSGNative.SectionRank.LocalDet
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure SylowCentralData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  rk1 : Nat
  rk2 : Nat
  ok1 : Nat
  ok2 : Nat
  nP : Nat
  rx : Nat
  ry : Nat
  t : Nat

@[expose] def SylowCentralData.regsLt (D : SylowCentralData) : Bool :=
  [D.rk1, D.rk2, D.rx, D.ry].all (decide <| · < D.nregs)

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def sylowGenFacts (D : SylowCentralData) (K1 K2 : M) : Bool :=
  decide (0 < D.ok1) && decide (0 < D.ok2) && O.eq (O.pow K1 D.ok1) O.one &&
    O.eq (O.pow K2 D.ok2) O.one

@[expose] def centralFacts (K1 K2 X Y : M) : Bool :=
  O.commOK X K1 && O.commOK X K2 && O.commOK Y K1 && O.commOK Y K2

@[expose] def sylowCentralFacts [Inhabited M] [Inhabited V] (D : SylowCentralData) (R E : Array M)
    (par lab : Array Nat) (cl : Array (Array Nat)) : Bool :=
  O.sylowGenFacts D R[D.rk1]! R[D.rk2]! &&
    O.enumOK #[R[D.rk1]!, R[D.rk2]!] D.nP D.t E par lab cl &&
    O.qFacts E R[D.rx]! R[D.ry]! D.t && O.centralFacts R[D.rk1]! R[D.rk2]! R[D.rx]! R[D.ry]!

@[expose] def sylowCentralCheck [Inhabited M] [Inhabited V] (D : SylowCentralData) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let En := O.enumBFS #[R[D.rk1]!, R[D.rk2]!] D.nP
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.regsLt &&
    O.sylowCentralFacts D R En.1 En.2.1 En.2.2.1 En.2.2.2

end Ops

@[expose] def j3SylowCentralData : SylowCentralData where
  seedA := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 29
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 4 4 5, .mul 2 5 6, .mul 3 3 7, .mul 3 7 8,
      .mul 8 8 9, .pow 18 9 10, .mul 10 6 11, .mul 11 9 12, .mul 2 2 13, .mul 13 13 14,
      .mul 14 14 15, .mul 2 15 16, .pow 18 16 17, .mul 17 0 18, .mul 18 16 19,
      .pow 7 12 20, .mul 19 20 21, .mul 21 19 22, .mul 22 12 23,
      .mul 12 19 24, .mul 24 20 25, .mul 25 19 26, .pow 3 23 27, .pow 3 26 28]
  rk1 := 23
  rk2 := 26
  ok1 := 9
  ok2 := 9
  nP := 243
  rx := 27
  ry := 28
  t := 0

end CFSG.SectionRank.Native
