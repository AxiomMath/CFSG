module

public import Certificates.Data.Seitz77Sec27SmallU42
public meta import Certificates.Data.Seitz77Sec27SmallU42
import Certificates.Kernel.Sporadic.PSp45.Census

public section

namespace Certificates

open CertificateChecks

theorem certificate6129 : Seitz77Sec27.u42CensusCheck = true :=
  KernelSpor.PSp45.c6129census

end Certificates
