module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Co2Smith.GlCosetInputs
public meta import CFSG.Sporadic.Co2Smith.GlCosetInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

meta def chCzS : Array (Array Nat) := glExtend (glOrig glCzWords) glChainCzW

meta def chCzB : Array Nat := glChainCzBase.toArray

@[expose] def chCzD : List (List Int) := glChainCzW.toList.drop glCzWords.length

meta def chCzG : Array (Array Nat) := (glCzWords.map fun w => glPermArr (glR w)).toArray

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.CzGP CertificateChecks.KernelCo2Smith.chCzG 12

#ks_raworb_data CertificateChecks.KernelCo2Smith.CCz 2300 12 256
  CertificateChecks.KernelCo2Smith.chCzS CertificateChecks.KernelCo2Smith.chCzB 21
  CertificateChecks.KernelCo2Smith.chCzD
