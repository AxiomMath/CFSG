module

public import Certificates.Kernel.Census.Fi22RDefsT1
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkT1R
import Certificates.Kernel.Census.Fi22PkT1A
import Certificates.Kernel.Census.Fi22PkT1W
import Certificates.Kernel.Census.Fi22PkT1K
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

namespace CertificateChecks.KernelCensus.Fi22K.T1

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kH2 : ppcHeadAt 3510 12 (fi22T1Xs.drop 2) (fi22T1Rs.drop 2) (fi22T1Cjs.drop 2)
    (fi22T1Bs.drop 2) = true := by
  quickRfl

theorem kH3 : ppcHeadAt 3510 12 (fi22T1Xs.drop 3) (fi22T1Rs.drop 3) (fi22T1Cjs.drop 3)
    (fi22T1Bs.drop 3) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
