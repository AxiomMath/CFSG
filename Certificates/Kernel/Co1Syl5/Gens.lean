module

public import Certificates.Kernel.Co1Syl5.In

public section

namespace CertificateChecks.KernelCo1Syl5

open CFSG.Sporadic.Co1Schreier.Native

def sylGens : Array (Array Nat) := #[sylDag.1.getD 40 one, sylDag.1.getD 38 one]

end CertificateChecks.KernelCo1Syl5

end
