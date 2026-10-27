module

public import CFSG.RankThree.Co2.WFacts
import Certificates.Kernel.Co2Cen.Facts110

public section

namespace Certificates

open CertificateChecks

theorem certificate8110 : CFSG.RankThree.Co2.WFacts :=
  KernelSpor.Co2Cen.wFacts

end Certificates
