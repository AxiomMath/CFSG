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

@[expose] noncomputable def keyD43g2 (c : Nat) : Bool := keyChunk KT (RL.getD 2 []) (tabAt GX.F 2) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.keyD43g2 0 104 1 as CertificateChecks.KernelD43.d43key2_

namespace CertificateChecks.KernelD43

#kc_forall_chunks keys2 (fun c => keyD43g2 c = true) 104 CertificateChecks.KernelD43.d43key2_ 1

end CertificateChecks.KernelD43

end
