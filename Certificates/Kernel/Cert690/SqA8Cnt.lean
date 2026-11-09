module

public import Certificates.Data.Kernel.Cert690.SqA8K
public import Certificates.Kernel.Cert690.SqPassData
public import Certificates.Kernel.Cert690.SqA8WData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem cntOK : a8T r1 r2 Ws = true := by
  have h : a8K r1 r2 Ws = true := by quickRfl
  exact (a8K_eq r1 r2 Ws).symm.trans h

end CertificateChecks.KernelC690.SqPass

end
