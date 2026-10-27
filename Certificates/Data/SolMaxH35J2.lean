module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.SolMax.H35.J2

open CFSG.Monster.B.Co2.Native

@[expose] def c1 : Array Nat := CFSG.ComponentClassification.J2Cover.cent2BStrong[0]!

@[expose] def c2 : Array Nat := CFSG.ComponentClassification.J2Cover.cent2BStrong[1]!

@[expose] def gArr : Array Nat := compA 315 c1 c1

@[expose] def hArr : Array Nat := compA 315 (compA 315 c1 c1) (compA 315 c2 c2)

@[expose] def dArr : Array Nat := compA 315 gArr hArr

@[expose] def pow5A (t : Array Nat) : Array Nat :=
  compA 315 t (compA 315 t (compA 315 t (compA 315 t t)))

@[expose] def j2H35Check : Bool :=
  eqA 315 (pow5A gArr) (idA 315) && eqA 315 (pow5A hArr) (idA 315) &&
    eqA 315 (compA 315 dArr dArr) (idA 315) && !(eqA 315 dArr (idA 315)) &&
    CFSG.ComponentClassification.J2Cover.fixedCount 315 dArr == 11

end CFSG.ComponentClassification.SolMax.H35.J2
