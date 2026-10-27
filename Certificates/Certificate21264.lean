
module

public import Certificates.Kernel.SmithEK.GlueX

public section

namespace Certificates

theorem certificate21264 :
    CFSG.SmithE.chkColl () = true :=
  CertificateChecks.KernelSmithEK.chkColl_eq

end Certificates
