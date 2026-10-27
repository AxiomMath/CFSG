module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairData
import Certificates.Kernel.Co1B.C27202

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Co1Pair in
theorem certificate27202 : cpOK = true := KernelCo1B.Pair27202.c27202

end Certificates
