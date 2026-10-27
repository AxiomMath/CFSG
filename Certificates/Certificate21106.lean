module

public import Certificates.Kernel.SmithEK.ChkP

public section

namespace Certificates

theorem certificate21106 :
    CFSG.SmithE.chkP = true :=
  CertificateChecks.KernelSmithEK.chkP_eq

end Certificates
