module

public import CFSG.RankThree.Co2.SylFacts
import Certificates.Kernel.Co2Syl.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate8113 : CFSG.RankThree.Co2.SylFacts :=
  KernelSpor.Co2Syl.sylFacts

end Certificates
