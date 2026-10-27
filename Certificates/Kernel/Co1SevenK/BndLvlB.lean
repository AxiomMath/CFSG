module

public import Certificates.Kernel.Co1SevenK.BndData
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBoundP
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Co1BBoundP

@[expose] noncomputable def ch13698bB (n : Nat) : Bool :=
  lvlChunkP 7 CertificateChecks.KernelCo1B.Bound17591.XB BD.TB BD.CFB BD.NPB
    CertificateChecks.KernelCo1B.CV.F BD.CNB n

end CertificateChecks.KernelCo1SevenK

#kc_each CertificateChecks.KernelCo1SevenK.ch13698bB 0 54

end
