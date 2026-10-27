module

public import Certificates.Data.Kernel.Cert690.SqA8
public import Certificates.Kernel.Cert690.PglData
public import Certificates.Kernel.Cert690.SqPglData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690 CertificateChecks.KernelC690.Pgl

set_option maxHeartbeats 0 in
theorem passNegMask : passGo (idxT S) (idxT W1) K.length M2 r1 K (invsL K) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem passNegTree : passGo (idxT S) (idxT W2) K.length M1 r1 K (invsL K) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bitsNeg : invBitsL M1 K 0 = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem invNeg : invOKL 4 [oneF, 2166376464, 12345] = false := by decide +kernel

end CertificateChecks.KernelC690.SqPgl

end
