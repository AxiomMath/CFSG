module

public import Certificates.Kernel.SmithEK.ChkT

public section

namespace Certificates

theorem certificate21105 :
    CFSG.SmithE.chkT = true :=
  CertificateChecks.KernelSmithEK.chkT_eq

end Certificates
