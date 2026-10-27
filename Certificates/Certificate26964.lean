module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveFinite
import Certificates.Kernel.HSStd.S5Three

public section

open CFSG.EvenSporadicStandard.HSStd

namespace Certificates

open CertificateChecks

theorem s5ThreeProp_true : S5ThreeProp := KernelHSStd.s5ThreeProp_kernel

open CFSG.EvenSporadicStandard.HSStd in
theorem certificate26964 : S5ThreeProp := s5ThreeProp_true

end Certificates
