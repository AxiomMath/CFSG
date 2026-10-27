module

public import CFSG.Sporadic.Co2Smith.GlNJInputs
public meta import CFSG.Sporadic.Co2Smith.GlNJInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

meta def njGtArrs : Array (Array Nat) :=
  (Array.range 3).map fun k =>
    CFSG.Sporadic.Co2Smith.Native.glNJPermR (CFSG.Sporadic.Co2Smith.Native.glNJGt k)

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.NJGP CertificateChecks.KernelCo2Smith.njGtArrs 12
