module

public import Certificates.Data.Kernel.D43.Cube
public import Certificates.Kernel.D43.HexP
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def cubeD43p (c : Nat) : Bool := cubeChunk PX.F 0 c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.cubeD43p 0 13 1 as CertificateChecks.KernelD43.d43cubep

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

#kc_forall_chunks phiCube (fun c => cubeD43p c = true) 13 CertificateChecks.KernelD43.d43cubep 1

theorem negCube : (!cubeChunk (fun j => if j = 0 then PX.F 1 else PX.F j) 0 0) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
