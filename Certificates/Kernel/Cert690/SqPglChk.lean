module

public import Certificates.Data.Kernel.Cert690.SqA8
public import Certificates.Data.Kernel.Cert690.SqA8T
public import Certificates.Kernel.Cert690.PglData
public import Certificates.Kernel.Cert690.SqPglData

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.SqPgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62
  CertificateChecks.KernelC690.Pgl

set_option maxHeartbeats 0 in
theorem pass1 : passGo (idxT S) (idxT W1) K.length M1 r1 K (invsL K) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pass2 : passGo (idxT S) (idxT W2) K.length M2 r2 K (invsL K) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invK : invOKL K.length K = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bitsK : invBitsL (Nat.lor M1 M2) K 0 = true := by decide +kernel

theorem bitsTop : (Nat.lor M1 M2).testBit 336 = false := by decide +kernel

theorem r12 : r1 = 2166376464 ∧ r2 = 1108378656 := by decide +kernel

theorem memR : (K.contains 2166376464 && K.contains 1108378656 && K0.contains 2166376464 &&
    !K0.contains 1108378656) = true := by decide +kernel

theorem invR : isInvCode 2166376464 = true ∧ isInvCode 1108378656 = true := by decide +kernel

theorem isoGens : kPGLGens.all (isoQ false) = true ∧ isoQ false Code.one = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem root1 : (innTab (2 * innW (compTab (liftTab 2166376464 0) (liftTab 2166376464 0))) ==
    compTab (liftTab 2166376464 0) (liftTab 2166376464 0)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem root2 : (innTab (2 * innW (compTab (liftTab 1108378656 0) (liftTab 1108378656 0))) ==
    compTab (liftTab 1108378656 0) (liftTab 1108378656 0)) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem rootV : rootF 2166376464 = 0 ∧ rootF 1108378656 = 0 := by decide +kernel

end CertificateChecks.KernelC690.SqPgl

end
