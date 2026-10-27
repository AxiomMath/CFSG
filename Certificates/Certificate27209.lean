module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ClassData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundLetters
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.G24Cls.C27209
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
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
import CFSG.Sporadic.Co1Block.TwoBComp

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Co1Cent CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2 in
theorem certificate27209 : ∀ j < 6, ∀ i < 8,
    wordM [permOfArr 1365 xa, permOfArr 1365 ya] (sWords.getD j []) * permOfArr 1365 rdGens[i]! *
        (wordM [permOfArr 1365 xa, permOfArr 1365 ya] (sWords.getD j []))⁻¹ ∈
      Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) :=
  KernelG24.Norm27209.norm_ok

end Certificates
