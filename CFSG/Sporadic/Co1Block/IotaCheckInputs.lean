module

public import CFSG.Sporadic.Co1Block.IotaData
public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.TextCheck
public meta import CFSG.Sporadic.Co2Cert.Cert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Schreier

@[noinline, expose] def iotaCheckOf (R₀ R₁ : CFSG.Sporadic.Co1Schreier.Native.Rows)
    (A : Array (Array Nat)) (Z U : Array Nat) (Q : Array (Array Nat)) : Bool :=
  let E := extendArrs A iotaDerivs
  (CFSG.Sporadic.Co1Schreier.Native.dag [R₀, R₁] iotaDerivs).2.2 &&
    extWordsOK 2 iotaDerivs && allInv E && eqA 2300 E[23]! Z && eqA 2300 E[51]! U &&
    allLt 8 fun k => eqA 2300 E[36 + k]! Q[k]!

end CFSG.Sporadic.Co1Block
