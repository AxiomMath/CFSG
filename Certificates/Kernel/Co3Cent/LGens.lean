module

public import Certificates.Data.Co3Cent

public section

namespace CertificateChecks.KernelCo3Cent

@[expose] def lGensC : Array (Array ℕ) := CFSG.HardMathSupport.Dickson.I271.Co3Cent.lGens ()

@[expose] def keysC : Array ℕ := #[0, 1, 2, 3, 4, 5, 6]

end CertificateChecks.KernelCo3Cent

end
