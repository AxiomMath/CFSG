module

public import CFSG.Sporadic.Co2Smith.GlC0QuotInputs
public meta import CFSG.Sporadic.Co2Smith.GlC0QuotInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

meta def qtArrs : Array (Array Nat) :=
  #[CFSG.Sporadic.Co2Smith.Native.glPermArr
    (CFSG.Sporadic.SmallF2.Native.mulRows 22 CFSG.Sporadic.Co2Smith.Native.glGa
      CFSG.Sporadic.Co2Smith.Native.glZ)]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.QP CertificateChecks.KernelCo2Smith.qtArrs 12
