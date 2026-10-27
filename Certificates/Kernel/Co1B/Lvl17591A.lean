module

public import Certificates.Kernel.Co1B.Data17591
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Data.Kernel.Co1BBound
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17591

open CFSG.KC.Co1BBound

@[expose] noncomputable def chunkA (n : Nat) : Bool := lvlChunkK XB K.T K.CF CV.F K.CN n

end CertificateChecks.KernelCo1B.Bound17591

#kc_each CertificateChecks.KernelCo1B.Bound17591.chunkA 0 27

end
