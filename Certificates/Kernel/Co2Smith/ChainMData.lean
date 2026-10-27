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

meta def chMS : Array (Array Nat) := glExtend (glOrig glMWords) glChainMW

meta def chMB : Array Nat := glChainMBase.toArray

@[expose] def chMD : List (List Int) := glChainMW.toList.drop glMWords.length

meta def chMG : Array (Array Nat) := (glMWords.map fun w => glPermArr (glR w)).toArray

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.MGP CertificateChecks.KernelCo2Smith.chMG 12

#ks_rawchain_sl2_data CertificateChecks.KernelCo2Smith.CM 2300 12 8 256
  CertificateChecks.KernelCo2Smith.chMS CertificateChecks.KernelCo2Smith.chMB 4
  CertificateChecks.KernelCo2Smith.chMD
