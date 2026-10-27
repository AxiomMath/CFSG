module

public import CFSG.RankThree.Co2.TInvFacts
import Certificates.Kernel.Co2Census.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate8101 : CFSG.RankThree.Co2.TInvFacts :=
  KernelSpor.Co2TInv.tInvFacts

end Certificates
