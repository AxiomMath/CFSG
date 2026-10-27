module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.TwoB
import Certificates.Kernel.Co1FiveK.GlueB
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
import CFSG.Sporadic.Co1.Module.InvPermChar

public section

namespace Certificates

open CertificateChecks

theorem certificate13670 : Timmesfeld.Co1Five.globalOK CFSG.Sporadic.Co1.Native.co1Data.rowsA
    CFSG.Sporadic.Co1.Native.co1Data.rowsB = true :=
  KernelCo1FiveK.globalOK_eq_true

end Certificates
