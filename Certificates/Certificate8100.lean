module

public import CFSG.RankThree.Co2.C4Facts
import Certificates.Kernel.Co2Cen.Facts100

public section

namespace Certificates

open CertificateChecks

theorem certificate8100 : CFSG.RankThree.Co2.C4Facts :=
  KernelSpor.Co2Cen.c4Facts

end Certificates
