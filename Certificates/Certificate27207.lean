module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentData
import Certificates.Kernel.Co1B.C27207

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Co1Cent in
theorem certificate27207 : centOK = true := KernelCo1B.Cent27207.c27207

end Certificates
