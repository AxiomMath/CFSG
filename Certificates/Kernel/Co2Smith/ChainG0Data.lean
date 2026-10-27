module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.Sporadic.Co2Smith.GlDataRootInputs
public meta import CFSG.Sporadic.Co2Smith.GlDataRootInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat
public meta import CFSG.Sporadic.Co2Smith.Cat
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native

meta def chG0S : Array (Array Nat) := glExtend (glOrig glG0Words) glChainG0W

meta def chG0B : Array Nat := glChainG0Base.toArray

@[expose] def chG0D : List (List Int) := glChainG0W.toList.drop glG0Words.length

meta def chG0G : Array (Array Nat) := (glG0Words.map fun w => glPermArr (glR w)).toArray

@[expose] def rtR (k : Nat) : Nat := if k < 36 then k / 3 else k - 24

@[expose] def rtT (k : Nat) : Nat := if k < 36 then k % 3 + 1 else 1

meta def rtG : Array (Array Nat) :=
  (Array.ofFn (n := 42) fun k => glPermArr (glRootRows
    (if k.val < 36 then k.val / 3 else k.val - 24) (if k.val < 36 then k.val % 3 + 1 else 1))).push
    (glPermArr glGa)

end CertificateChecks.KernelCo2Smith

#kmisc_packarrs CertificateChecks.KernelCo2Smith.G0GP CertificateChecks.KernelCo2Smith.chG0G 12
#kmisc_packarrs CertificateChecks.KernelCo2Smith.RTP CertificateChecks.KernelCo2Smith.rtG 12

#ks_rawchain_sl2_data CertificateChecks.KernelCo2Smith.CG0 2300 12 8 256
  CertificateChecks.KernelCo2Smith.chG0S CertificateChecks.KernelCo2Smith.chG0B 13
  CertificateChecks.KernelCo2Smith.chG0D
