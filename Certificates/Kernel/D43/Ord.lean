module

public import Certificates.Data.Kernel.D43.Twin
public import Certificates.Kernel.D43.Data
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

@[expose] noncomputable def ordD43 (c : Nat) : Bool := ordChunk KT OT c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.ordD43 0 13 1 as CertificateChecks.KernelD43.d43ord

namespace CertificateChecks.KernelD43

#kc_forall_chunks ordAll (fun c => ordD43 c = true) 13 CertificateChecks.KernelD43.d43ord 1

end CertificateChecks.KernelD43

end
