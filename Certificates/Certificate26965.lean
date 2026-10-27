module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveData
import Certificates.Kernel.HS100.S5CFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd in
theorem certificate26965 : s5cOK = true := KernelHS100.s5cOK_eq

end Certificates
