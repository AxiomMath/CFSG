module

public import CFSG.Sporadic.Co2Smith.GlC0JkInputs
public meta import CFSG.Sporadic.Co2Smith.GlC0JkInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

meta def jkRowsM : Array (Array Nat) := CFSG.Sporadic.Co2Smith.Native.glJkO

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.JO CertificateChecks.KernelCo2Smith.jkRowsM 22
