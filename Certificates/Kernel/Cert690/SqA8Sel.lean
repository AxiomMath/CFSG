module

public import Certificates.Data.Kernel.Cert690.SqA8T
public import Certificates.Data.Kernel.Cert690.Pgl
public import Certificates.Kernel.Cert690.GrpPData
public import Certificates.Kernel.Cert690.SqPassData
public import Certificates.Kernel.Cert690.SqA8WData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CertificateChecks.KernelC690.GrpP CFSG.LargeExtraspecial.O62

set_option maxHeartbeats 0 in
theorem selOm : ((involL Om).filter fun g => Code.act g 1 == 1) = Ws.map Prod.fst := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cmOm : Ws.all (cmK (idxT Sm) (idxT W1) (idxT W2) Om.length M1 M2) = true := by
  decide +kernel

end CertificateChecks.KernelC690.SqPass

end
