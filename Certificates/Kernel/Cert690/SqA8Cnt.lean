module

public import Certificates.Data.Kernel.Cert690.SqA8T
public import Certificates.Kernel.Cert690.SqPassData
public import Certificates.Kernel.Cert690.SqA8WData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690

set_option maxHeartbeats 0 in
theorem cntOK : a8T r1 r2 Ws = true := by decide +kernel

end CertificateChecks.KernelC690.SqPass

end
