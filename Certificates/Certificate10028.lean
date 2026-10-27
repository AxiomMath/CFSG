module

public import CFSG.Monster.GMS.ASegConnCo1Inputs
import Certificates.Kernel.Co1M.Diam10028Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.ASegConn in
theorem certificate10028 :
    diamCheck = true :=
  KernelCo1M.Diam.diam_ok KernelCo1M.Diam.diam_all

end Certificates
