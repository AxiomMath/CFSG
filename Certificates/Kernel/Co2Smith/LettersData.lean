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

meta def smRows : Array (Array Nat) :=
  CFSG.Sporadic.Co2Smith.Native.letters CFSG.Sporadic.Co2Smith.seedRowsArr

meta def glRowsM : Array (Array Nat) := CFSG.Sporadic.Co2Smith.Native.glRows

meta def formRowsM : Array (Array Nat) :=
  #[CFSG.Sporadic.Co2Smith.Native.glForm 0, CFSG.Sporadic.Co2Smith.Native.glForm 1,
    CFSG.Sporadic.Co2Smith.Native.glForm 2]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.SM CertificateChecks.KernelCo2Smith.smRows 22
#kmisc_packarrs CertificateChecks.KernelCo2Smith.LP CertificateChecks.KernelCo2Smith.glRowsM 22
#kmisc_packarrs CertificateChecks.KernelCo2Smith.FM CertificateChecks.KernelCo2Smith.formRowsM 22
