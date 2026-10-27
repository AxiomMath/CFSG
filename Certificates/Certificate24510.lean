module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
import Certificates.Kernel.Co1B.C24510

public section

namespace Certificates

open CertificateChecks

theorem certificate24510 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.perfectCheckA = true := KernelCo1B.H24510.c24510

end Certificates
