module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerData
import Certificates.Kernel.HS3850.InnerKGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate117011 : CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert.innerOK = true := KernelHS3850.innerK

end Certificates

end
