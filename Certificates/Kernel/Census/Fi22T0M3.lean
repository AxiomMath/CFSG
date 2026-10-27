module

public import Certificates.Kernel.Census.Fi22RDefsT0
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkT0R
import Certificates.Kernel.Census.Fi22PkT0A
import Certificates.Kernel.Census.Fi22PkT0W
import Certificates.Kernel.Census.Fi22PkT0K
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

namespace CertificateChecks.KernelCensus.Fi22K.T0

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kM0g : (Nat.beq fi22T0Root.ga.size fi22T0Root.gams.size && Nat.beq fi22T0Root.gi.size fi22T0Root.gams.size &&
    (List.range fi22T0Root.gams.size).all (fun l =>
      Nat.blt fi22T0Root.gams[l]!.1 fi22T0Root.cs.size && Nat.blt fi22T0Root.gams[l]!.2 fi22T0Root.cs.size &&
      Nat.beq fi22T0Root.ga[l]! (pcomm 3510 12 fi22T0Root.cs[fi22T0Root.gams[l]!.1]! fi22T0Root.cs[fi22T0Root.gams[l]!.2]!) &&
      Nat.beq fi22T0Root.gi[l]! (pcomm 3510 12 fi22T0Root.cs[fi22T0Root.gams[l]!.2]! fi22T0Root.cs[fi22T0Root.gams[l]!.1]!))) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
