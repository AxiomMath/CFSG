module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
public meta import CFSG.Sporadic.Co2Smith.GlDataInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

meta def arcPerms : Array (Array Nat) := #[glPermArr glAl, glPermArr glGa, glPermArr glZ]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.AP CertificateChecks.KernelCo2Smith.arcPerms 12
