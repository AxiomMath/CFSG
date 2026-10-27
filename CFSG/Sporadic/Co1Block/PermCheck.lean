
module

public import CFSG.Sporadic.Co1Block.PermCheckBase

public import CFSG.Sporadic.Co1Block.PermData
public import CFSG.Sporadic.Schreier.Co1StabFix
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Co1Block.PermCheckInputs
public import Certificates.Certificate2043

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

theorem perm_check : permCheckOf certVecs (certAct 0) (certAct 1)
    CFSG.Sporadic.Co1Schreier.Native.aR CFSG.Sporadic.Co1Schreier.Native.bR = true :=
  Certificates.certificate2043

end CFSG.Sporadic.Co1Block
