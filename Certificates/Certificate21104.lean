module

public import Certificates.Kernel.SmithEK.ChkW

public section

namespace Certificates

theorem certificate21104 :
    CFSG.SmithE.chkW = true :=
  CertificateChecks.KernelSmithEK.chkW_eq

end Certificates
