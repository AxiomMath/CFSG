module

public import Certificates.Data.Kernel.D43.Twin
public import Certificates.Kernel.D43.Data
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def keyD43g4 (c : Nat) : Bool := keyChunk KT (RL.getD 4 []) (tabAt GX.F 4) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.keyD43g4 0 104 1 as CertificateChecks.KernelD43.d43key4_

namespace CertificateChecks.KernelD43

#kc_forall_chunks keys4 (fun c => keyD43g4 c = true) 104 CertificateChecks.KernelD43.d43key4_ 1

end CertificateChecks.KernelD43

end
