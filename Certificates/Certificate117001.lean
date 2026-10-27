module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
import Certificates.Kernel.Misc.Perm.HS100.TSyGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus in
theorem certificate117001 : zasSylowOK = true := KernelMisc.HS100.T.zasSylowOK_true

end Certificates
