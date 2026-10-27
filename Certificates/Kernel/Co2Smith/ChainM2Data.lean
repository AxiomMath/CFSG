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

meta def chM2S : Array (Array Nat) := glExtend (glOrig glM2Words) glChainM2W

meta def chM2B : Array Nat := glChainM2Base.toArray

@[expose] def chM2D : List (List Int) := glChainM2W.toList.drop glM2Words.length

meta def chM2G : Array (Array Nat) := (glM2Words.map fun w => glPermArr (glR w)).toArray

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.M2GP CertificateChecks.KernelCo2Smith.chM2G 12

#ks_rawchain_sl2_data CertificateChecks.KernelCo2Smith.CM2 2300 12 8 256
  CertificateChecks.KernelCo2Smith.chM2S CertificateChecks.KernelCo2Smith.chM2B 3
  CertificateChecks.KernelCo2Smith.chM2D
