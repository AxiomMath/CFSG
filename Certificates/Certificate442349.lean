module

public import Certificates.Data.T84P
import CFSG.Certificates.Kernel.Misc.T84Sound
import Certificates.Kernel.Misc.T84.Checks

public section

namespace Certificates

open CertificateChecks.KernelMisc.T84 in
theorem certificate442349 : T84P.Facts :=
  CFSG.KC.Misc.T84.facts_of_kernel ch442349_d0 ch442349_s0 ch442349_p0 ch442349_vf ch442349_j
    ch442349_cent ch442349_y ch442349_rank ch442349_only

end Certificates
