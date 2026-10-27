module

public import Certificates.Data.Kernel.Cert690.SqPass
public import Certificates.Data.Kernel.Cert690.Pgl
public import Certificates.Kernel.Cert690.GrpPData
public import Certificates.Kernel.Cert690.SqPassData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CertificateChecks.KernelC690.GrpP

set_option maxHeartbeats 0 in
theorem pass1 : passGo (idxT Sm) (idxT W1) Om.length M1 r1 Om (invsL Om) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pass2 : passGo (idxT Sm) (idxT W2) Om.length M2 r2 Om (invsL Om) = true := by
  decide +kernel

end CertificateChecks.KernelC690.SqPass

end
