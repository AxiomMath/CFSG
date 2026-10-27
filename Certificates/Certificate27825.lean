
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmCheck
import Certificates.Kernel.Census.Pg.AdmGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate27825 : CFSG.EvenSporadicStandard.Fin76b.W16.admCheck = true := KernelPgAdm.facts27825

end Certificates
