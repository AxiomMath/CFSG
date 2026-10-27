module

public meta import Certificates.Data.CFSGNative.Co2Smith.Pin
meta import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2SmithS

meta def stdM : Array (Array Nat) := CFSG.Sporadic.Co2Smith.Native.stdRows ()

end CertificateChecks.KernelCo2SmithS

#kmisc_packarrs CertificateChecks.KernelCo2SmithS.SR CertificateChecks.KernelCo2SmithS.stdM 8

end
