module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
import Certificates.Kernel.Sporadic.OddCore.Suz26680F

public section

namespace Certificates

open CertificateChecks

theorem certificate26680 : CFSG.EvenSporadicStandard.Solomon78.suzRowCheck = true := KernelSpor.S26680.check26680

end Certificates
