module

public import Certificates.Kernel.Co1P.Defs21150
public import Certificates.Data.Kernel.Co1PRecsOK

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1P

@[expose] noncomputable def recA4_chunk (c : Nat) : Bool := chunkK 60479 (recAtK 8 rA4) c

end CertificateChecks.KernelCo1P

end
