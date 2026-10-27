module

public import Certificates.Data.Kernel.D43.Base
public import Certificates.Kernel.D43.HexG
public import Certificates.Kernel.D43.HexP
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def relD43 (c : Nat) : Bool := relChunk GX.F PX.F c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.relD43 0 39 1 as CertificateChecks.KernelD43.d43rel

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

#kc_forall_chunks relAll (fun c => relD43 c = true) 39 CertificateChecks.KernelD43.d43rel 1

theorem phiPts : tabAt PX.F 0 4 = 15 ∧
    ([0, 6, 479, 26571, 15916, 186, 1, 2].all fun p => tabAt PX.F 0 p == p) = true := by
  decide +kernel

theorem negRel : wOK GX.F PX.F [3] = false := by
  decide +kernel

theorem negRelPhi : wOK GX.F PX.F [16] = false := by
  decide +kernel

end CertificateChecks.KernelD43

end
