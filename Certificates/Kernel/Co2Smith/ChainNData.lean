module

public import Certificates.Kernel.Sporadic.RawGenSplit
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

meta def chNS : Array (Array Nat) := glExtend (glOrig glNWords) glChainNW

meta def chNB : Array Nat := glChainNBase.toArray

@[expose] def chND : List (List Int) := glChainNW.toList.drop glNWords.length

meta def chNG : Array (Array Nat) := (glNWords.map fun w => glPermArr (glR w)).toArray

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.NGP CertificateChecks.KernelCo2Smith.chNG 12

#ks_rawchain_sl2_data CertificateChecks.KernelCo2Smith.CN 2300 12 8 256
  CertificateChecks.KernelCo2Smith.chNS CertificateChecks.KernelCo2Smith.chNB 11
  CertificateChecks.KernelCo2Smith.chND
