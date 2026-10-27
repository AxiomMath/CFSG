module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsData
import Certificates.Kernel.Census.Cls24140
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Wong77.Cls in
theorem certificate24140 : clsCheck = true := KernelCensus.Cls24140.cls

end Certificates
