module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjCheck
import Certificates.Kernel.Co2Chain.W16Surj27823Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate27823 : CFSG.EvenSporadicStandard.Fin76b.W16.surjCheck = true := KernelCo2Chain.W16.check

end Certificates
