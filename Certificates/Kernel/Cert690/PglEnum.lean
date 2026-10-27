module

public import Certificates.Data.Kernel.Cert690.Enum
public import Certificates.Kernel.Cert690.PglData
public import CFSG.GF2Type.Smith1979W3.Cert690.Statements

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.Pgl

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

theorem lenK : K.length = 336 := by decide +kernel

theorem lenK0 : K0.length = 168 := by decide +kernel

theorem headK : K.head? = some oneF := by decide +kernel

theorem headK0 : K0.head? = some oneF := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixK : ixOK S K = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixK0 : ixOK S0 K0 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem bfsK : bfsOK (fun y => (idxT S).find y K.length) kPGLGens K par = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bfsK0 : bfsOK (fun y => (idxT S0).find y K0.length) kPGL0Gens K0 par0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem enumK : enumParK (fun i => (posT K).find i 0) kPGLGens K par 0 = true ∧
    enumClK (fun y => (idxT S).find y K.length) K.length kPGLGens K = true ∧
    enumInvK kPGLGens K = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem enumK0 : enumParK (fun i => (posT K0).find i 0) kPGL0Gens K0 par0 0 = true ∧
    enumClK (fun y => (idxT S0).find y K0.length) K0.length kPGL0Gens K0 = true ∧
    enumInvK kPGL0Gens K0 = true := by
  decide +kernel

end CertificateChecks.KernelC690.Pgl

end
