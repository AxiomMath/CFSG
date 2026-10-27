module

public import Certificates.Data.Kernel.D43.Cube
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def cubeD43g (c : Nat) : Bool :=
  cubeChunk GX.F (Nat.div c (nat_lit 13)) (Nat.mod c (nat_lit 13))

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.cubeD43g 0 104 1 as CertificateChecks.KernelD43.d43cubeg

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

#kc_forall_chunks genCube (fun c => cubeD43g c = true) 104 CertificateChecks.KernelD43.d43cubeg 1

theorem negGenCube : (!cubeChunk (fun j => if j = 0 then GX.F 1 else GX.F j) 0 0) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
