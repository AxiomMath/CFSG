module

public import Certificates.Data.A7T3
import Certificates.Kernel.A7T3.C7157

public section

namespace Certificates

theorem certificate7157 : A7T3.a7Check = true :=
  decide_eq_true CertificateChecks.KernelA7T3.stmt_true

end Certificates
