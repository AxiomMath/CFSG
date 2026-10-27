module

public import Certificates.Data.GH74J2CentCheck
public meta import Certificates.Data.GH74J2CentCheck

public section

namespace CFSG.Sporadic.J2

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.Generic.S45.EvSpor

@[expose] def commSqT (e g : Table) : Table :=
  compT 315 (commutatorT 315 e g) (commutatorT 315 e g)

@[expose] def j2CommSqOK : Bool :=
  j2C2A.all fun g => !involOK 315 g || memT 315 j2E g ||
    j2E.any fun e => !tblEq 315 (commSqT e g) (idT 315)

@[expose] def j2EInvs : Array Table := j2E.filter (involOK 315)

@[expose] def j2ERankOK : Bool :=
  j2EInvs.all fun x => j2EInvs.all fun y => j2EInvs.all fun z =>
    !(commTT 315 x y && commTT 315 x z && commTT 315 y z) || tblEq 315 y x || tblEq 315 z x ||
      tblEq 315 z y || tblEq 315 z (compT 315 x y)

@[expose] def j2C2BSqOK : Bool :=
  j2C2B.all fun x => !tblEq 315 (powT 315 4 x) (idT 315) || tblEq 315 (powT 315 2 x) (idT 315)

@[expose] def j2CentEACheck : Bool := j2CommSqOK && j2ERankOK && j2C2BSqOK

end CFSG.Sporadic.J2
