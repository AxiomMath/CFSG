module

public import Certificates.Kernel.Census.Fi22RDefsT2
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkT2R
import Certificates.Kernel.Census.Fi22PkT2A
import Certificates.Kernel.Census.Fi22PkT2W
import Certificates.Kernel.Census.Fi22PkT2K
import Certificates.Kernel.Census.Fi22PkU
import Certificates.Data.Kernel.Census.PackedRootBit
import Certificates.Data.Kernel.Census.PackedRoot
import Certificates.Data.Kernel.Census.Packed
import Certificates.Data.Kernel.Census.PackedConj
import Certificates.Data.Kernel.Census.PackedConjF
import CFSG.Certificates.Kernel.Enum.Defs
import Certificates.Kernel.Sporadic.Fi22.X2069P
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM0g : (Nat.beq fi22T2Root.ga.size fi22T2Root.gams.size && Nat.beq fi22T2Root.gi.size fi22T2Root.gams.size &&
    (List.range fi22T2Root.gams.size).all (fun l =>
      Nat.blt fi22T2Root.gams[l]!.1 fi22T2Root.cs.size && Nat.blt fi22T2Root.gams[l]!.2 fi22T2Root.cs.size &&
      Nat.beq fi22T2Root.ga[l]! (pcomm 3510 12 fi22T2Root.cs[fi22T2Root.gams[l]!.1]! fi22T2Root.cs[fi22T2Root.gams[l]!.2]!) &&
      Nat.beq fi22T2Root.gi[l]! (pcomm 3510 12 fi22T2Root.cs[fi22T2Root.gams[l]!.2]! fi22T2Root.cs[fi22T2Root.gams[l]!.1]!))) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
