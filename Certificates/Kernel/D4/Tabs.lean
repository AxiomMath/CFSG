module

public import Certificates.Kernel.D4.Hex

public section

namespace CertificateChecks.KernelD4

@[expose] noncomputable def LX (j : Nat) : Nat := HX.F (Nat.add 4 j)

@[expose] noncomputable def HT (j : Nat) : Nat := HX.F (Nat.add 35 j)

end CertificateChecks.KernelD4

end
