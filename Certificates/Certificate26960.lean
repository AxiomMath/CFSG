module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntData
import Certificates.Kernel.HS100.S5KGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd in
theorem certificate26960 : s5SylowOK = true := KernelHS100.S5K.s5SylowOK_true

end Certificates
