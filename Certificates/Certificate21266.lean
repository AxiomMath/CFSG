module

public import Certificates.Kernel.SmithEK.ChkD2

public section

namespace Certificates

theorem certificate21266 : CFSG.SmithE.chkDist2 = true :=
  CertificateChecks.KernelSmithEK.chkDist2_eq

end Certificates
