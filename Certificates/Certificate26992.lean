module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBase
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.G24Cls.C26992
import CFSG.Sporadic.Co1Block.TwoBCheckInputs
meta import CFSG.Sporadic.Co1Block.TwoBData
meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
meta import CFSG.Sporadic.Co1Block.CentCheck
meta import CFSG.Sporadic.Schreier.TitsBasic
meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
meta import CFSG.Sporadic.Schreier.Co1ChainCheck
meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
meta import Certificates.Data.CFSGNative.Co1Schreier.Base
meta import Certificates.Data.CFSGNative.Co1.Data
meta import Certificates.Data.CFSGNative.Co1.Involutions
meta import Certificates.Data.CFSGNative.Co1.TwoB
meta import Certificates.Data.CFSGNative.HS.SmallF2
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Certificates.Data.CFSGNative.Schreier.Merge
meta import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
meta import CFSG.Sporadic.Co1Block.ConjBData
meta import CFSG.Sporadic.Co1.Module.InvData
meta import CFSG.Sporadic.Co1.Module.Forms
meta import CFSG.Sporadic.Co1.Module.Orbits
import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
import Certificates.Data.CFSGNative.Co1.Data
import Certificates.Certificate10070
import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
import CFSG.Sporadic.Co1Block.TwoBComp

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 in
theorem certificate26992 : ∃ u ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
    ∃ v ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      u * u = 1 ∧ v * v = 1 ∧ (u * v) ^ 4 = 1 ∧ u * v ≠ v * u :=
  KernelG24.Dih26992.d8_ok

end Certificates
