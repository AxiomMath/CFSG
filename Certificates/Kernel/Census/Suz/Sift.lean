module

public import Certificates.Kernel.Census.Suz.Data
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Census.PackedExc
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzData
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzData

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCensus.SuzE0T
  CFSG.ComponentClassification.RankTwoSporadic.Suz.suzE0Text

#kmisc_hexflat CertificateChecks.KernelCensus.SuzE0T
  CFSG.ComponentClassification.RankTwoSporadic.Suz.suzE0Text 3 1782 11 2

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

@[expose] noncomputable def inMP (P : Nat) : Bool :=
  siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 P

@[expose] noncomputable def inTP (P : Nat) : Bool := inMP P || inMP (pc 1782 11 Suz2306.V P)

@[expose] def suzPSL : List Nat := [0, 1, 2, 3, 4, 8]

@[expose] noncomputable def nodeQ (allowInX : Bool) (d : ConjDataP) (e0 : Array Nat) (i : Nat) :
    Bool :=
  let wt := pwitOK 1782 11 suzPSL inMP inMP false allowInX false d.nodes[i]!.basis cNL[i]!
    d.wcs[i]! d.nodes[i]!.wit
  penumOK 1782 11 d.nodes[i]!.basis suzPSL cNL[i]! &&
    cond d.nodes[i]!.wit.isMono wt (wt || pexcOK 1782 11 suzPSL inTP e0 cNL d.excs i)

@[expose] noncomputable def suzE0P : Array Nat := #[SuzE0T.F 0, SuzE0T.F 1]

end CertificateChecks.KernelCensus.Suz

end
