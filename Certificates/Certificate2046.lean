
module

public import Certificates.Certificate2046Base

public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1.Module.InvDataBase
public meta import CFSG.Sporadic.Co1.Module.FormsBase
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.Co1B.C2046

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Monster.B.Co2.Native in
theorem certificate2046 : (conjBCheckOf [aR, bR] conjBDerivs CFSG.Sporadic.Co1.Module.rowsSB = true)
    ∧ (tabSoundOf (Native.triTable twoBTris) twoBTris.toArray = true) := KernelCo1B.c2046

end Certificates
