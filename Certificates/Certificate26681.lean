module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuterCheck
import Certificates.Kernel.Sporadic.OddCore.Suz26681

public section

namespace Certificates

open CertificateChecks

theorem certificate26681 : CFSG.EvenSporadicStandard.Solomon78.suzOuterCheck = true := KernelSpor.SuzK0.check26681

end Certificates
