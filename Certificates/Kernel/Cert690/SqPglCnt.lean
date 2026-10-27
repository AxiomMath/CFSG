module

public import Certificates.Data.Kernel.Cert690.SqPglT
public import Certificates.Kernel.Cert690.PglData
public import Certificates.Kernel.Cert690.SqPglData
public import Certificates.Kernel.Cert690.SqPgl4Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CertificateChecks.KernelC690.Pgl

set_option maxHeartbeats 0 in
theorem selX : (outersL K K0 == Xs.map fun X => X.1.1) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem i0X : (involL K0 == I0) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cmX : Xs.all (fun X => cmK (idxT S) (idxT W1) (idxT W2) K.length M1 M2 X.1) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem frX : bAnd(pqFOK Fr Ar, bAnd(pqAOK 1108378656 Ar,
    pqAll 64 fun v => Nat.beq (pqL6 Ar (pqL6 Ar v)) v)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem recX : pqAllL (pqRecOK Fr Ar) Xs = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem csX : pqAllL (pqCs I0) Xs = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bodyX : certBits.all (fun b => Xs.all (pqBody Fr Ar b)) = true := by decide +kernel

end CertificateChecks.KernelC690.SqPgl

end
