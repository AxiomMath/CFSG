module

public import Certificates.Data.CoreE1Tits
import Certificates.Kernel.LocalComp.TitsE1.Glue

public section

namespace Certificates

theorem certificate753512 : Certificates.CoreE1Perm.check (Certificates.CoreE1Perm.titsE1Data ()) = true :=
  CertificateChecks.KernelLC.TitsE1.tits_e1

end Certificates
