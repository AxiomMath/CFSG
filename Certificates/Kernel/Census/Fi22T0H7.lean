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

theorem kH14 : ppcHeadAt 3510 12 (fi22T0Xs.drop 14) (fi22T0Rs.drop 14) (fi22T0Cjs.drop 14)
    (fi22T0Bs.drop 14) = true := by
  quickRfl

theorem kH15 : ppcHeadAt 3510 12 (fi22T0Xs.drop 15) (fi22T0Rs.drop 15) (fi22T0Cjs.drop 15)
    (fi22T0Bs.drop 15) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T0

end
