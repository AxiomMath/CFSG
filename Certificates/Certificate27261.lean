module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
import Certificates.Kernel.Misc.Perm.HS100.X3Glue

public section

open CFSG.EvenSporadicStandard.HSStd.FiveY

namespace Certificates

open CertificateChecks

theorem x3OK_true : x3OK = true := KernelMisc.HS100.X3.x3OK_true

theorem certificate27261 : CFSG.EvenSporadicStandard.HSStd.FiveY.x3OK = true := x3OK_true

end Certificates
