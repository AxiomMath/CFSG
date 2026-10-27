module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
import Certificates.Kernel.Co1B.C24511

public section

namespace Certificates

open CertificateChecks

theorem certificate24511 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.sylowCheckB = true := KernelCo1B.H24511.c24511

end Certificates
