module

public import Certificates.Kernel.D42Tri.P0Chk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelO8

@[expose] noncomputable def cubeK (x : Nat) : Nat := pq x (pq x x)

theorem ch17627_k2n : allN 216 (fun i => strictB (cubeK (K2.T i)) (fun u =>
    bIf(Nat.beq (cubeK u) pid, Nat.beq u pid, true))) = true := by
  quickRfl

end CertificateChecks.KernelD42Tri

end
