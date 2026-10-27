module

public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.XFix
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative

@[noinline, expose] def classCheckOf (V : Array Nat) (Ra Rc R₁ : Rows) : Bool :=
  xFixCount V Ra == 2280 && xFixCount V Rc == 264 && xFixCount V R₁ == 0 &&
    [Ra, Rc, R₁].all fun R => mul R R == one && validRows R && R != one

end CFSG.Sporadic.Co1Block
