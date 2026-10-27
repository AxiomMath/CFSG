module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Co2Smith.GlU62Inputs
public meta import CFSG.Sporadic.Co2Smith.GlU62Inputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

meta def chL1S : Array (Array Nat) := glExtend (glOrig u62L1Words) u62L1W

meta def chL1B : Array Nat := u62L1Base.toArray

@[expose] def chL1D : List (List Int) := u62L1W.toList.drop u62L1Words.length

meta def chL1G : Array (Array Nat) := (u62L1Words.map fun w => glPermArr (glR w)).toArray

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.L1GP CertificateChecks.KernelCo2Smith.chL1G 12

#ks_raworb_data CertificateChecks.KernelCo2Smith.CL1 2300 12 256
  CertificateChecks.KernelCo2Smith.chL1S CertificateChecks.KernelCo2Smith.chL1B 22
  CertificateChecks.KernelCo2Smith.chL1D
