module

public import CFSG.RankThree.Co2.ClassFacts
import Certificates.Kernel.Co2Cls.ClassFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate8102 : CFSG.RankThree.Co2.ClassFacts :=
  KernelSpor.Co2Cls.Facts8102.classFacts

end Certificates
