module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
import Certificates.Kernel.Co1B.C24512

public section

namespace Certificates

open CertificateChecks

theorem certificate24512 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.perfectCheckC = true := KernelCo1B.H24512.c24512

end Certificates
