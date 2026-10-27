module

public import Certificates.Kernel.SmithEK.ChkUA

public section

namespace Certificates

theorem certificate21263 :
    CFSG.SmithE.chkUA () = true :=
  CertificateChecks.KernelSmithEK.chkUA_eq

end Certificates
