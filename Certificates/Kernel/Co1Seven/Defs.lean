module

public import Certificates.Data.Kernel.Co1Three.Slp
public import Certificates.Kernel.Co1Seven.Data

public section

namespace CertificateChecks.KernelCo1Seven

open CFSG.KC.Co1Cl

@[expose] noncomputable def ch1023013slp (k : Nat) : Bool := chunkK TS CH WL k

@[expose] noncomputable def ch1023013eq (k : Nat) : Bool := eqsK TS (nat_lit 7) GL (getLLL Q k)

end CertificateChecks.KernelCo1Seven

end
