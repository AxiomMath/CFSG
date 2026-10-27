module

public import CFSG.Sporadic.Schreier.Co1Base
public import CFSG.Sporadic.Co1
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

namespace Native

open CFSG.Sporadic.Co1Schreier.Native

@[expose] def aR : Rows := CFSG.Sporadic.Co1.Native.co1Data.rowsA

@[expose] def bR : Rows := CFSG.Sporadic.Co1.Native.co1Data.rowsB

@[expose] def cR : Rows := mul aR bR

@[expose] def dR : Rows := mul (mul aR bR) bR

@[expose] def uR : Rows := mul (pow cR 2) dR

@[expose] def wR : Rows := mul (pow uR 2) cR

@[expose] def xR : Rows := mul (mul (pow (inv cR) 2) aR) (pow cR 2)

@[expose] def yR : Rows := mul (mul (pow (inv dR) 2) (pow wR 8)) (pow dR 2)

@[expose] def tR : Rows := mul (mul xR yR) xR

@[expose] def threeLocalCheck : Bool :=
  mul cR (inv cR) == one && mul dR (inv dR) == one && mul tR (inv tR) == one &&
    mul yR (inv yR) == one

end Native

namespace ThreeLocal

end ThreeLocal

end CFSG.Sporadic.Co1Schreier
