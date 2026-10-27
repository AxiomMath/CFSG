module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1LeviData
import Certificates.Kernel.OmegaEight.LeviCert

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model in
theorem certificate3374 : leviCheck = true := KernelO8.cert3374

end Certificates

end
