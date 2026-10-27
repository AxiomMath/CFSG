module

public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
public meta import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

meta def tRowsM : Array (Array Nat) := CFSG.Sporadic.Co2Smith.Native.glMkT

meta def tabBitsM : Array (Array Nat) :=
  let rel := CFSG.Sporadic.Co2Smith.Native.glMkRelTab
  let com := CFSG.Sporadic.Co2Smith.Native.glMkComTab
  #[Array.ofFn (n := 225) fun k => if (rel[k.val / 15]!)[k.val % 15]! then 1 else 0,
    Array.ofFn (n := 225) fun k => if (com[k.val / 15]!)[k.val % 15]! then 1 else 0]

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.TP CertificateChecks.KernelCo2Smith.tRowsM 22
#kmisc_packarrs CertificateChecks.KernelCo2Smith.TB CertificateChecks.KernelCo2Smith.tabBitsM 1
