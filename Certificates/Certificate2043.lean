
module

public import Certificates.Certificate2043Base

public import CFSG.Sporadic.Co1Block.PermCheckInputs
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.Co1B.C2043

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2.Native in
open CFSG.Monster.B.Co2.Native in
theorem certificate2043 : permCheckOf certVecs (certAct 0) (certAct 1)
    CFSG.Sporadic.Co1Schreier.Native.aR CFSG.Sporadic.Co1Schreier.Native.bR = true := KernelCo1B.c2043

end Certificates
