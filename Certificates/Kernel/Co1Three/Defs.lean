module

public import Certificates.Data.Kernel.Co1Three.Slp
public import Certificates.Kernel.Co1Three.Data

public section

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Co1Cl

@[expose] noncomputable def slpChunk (k : Nat) : Bool := chunkK TS CH WL k

@[expose] noncomputable def eqChunk (k : Nat) : Bool := eqsK TS (nat_lit 3) GL (getLLL Q k)

end CertificateChecks.KernelCo1Three

end
