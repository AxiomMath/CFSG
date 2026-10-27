
module

public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase

public import CFSG.Monster.B.Fischer.Fi22GraphData
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Monster.B.Fischer.Fi22GraphData
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import Certificates.Certificate3037
public import Certificates.Certificate3037Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

theorem fi22Graph_check :
    fi22GraphOuterHex.length = 3 * 3510 ∧
    isInvA 3510 fi22GraphOuterArr (invCand 3510 fi22GraphOuterArr) = true :=
  Certificates.certificate3037

end CFSG.Monster.B.Fischer
