module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Co1Inputs
import Certificates.Kernel.Co1M.C25050

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoB.MW3 in
theorem certificate25050 :
    commOK = true := KernelCo1M.c25050

end Certificates
