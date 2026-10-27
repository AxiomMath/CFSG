module

public import Certificates.Data.Co3TwistData

public section

namespace CertificateChecks.KernelCo3Tw

open CFSG.LocalAnalysis.GLTheoremA.H1017.Co3TwistNative

@[expose] def p3Gs : Array (Array Nat) := permsOf p3GensHex

end CertificateChecks.KernelCo3Tw

end
