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

theorem kH4 : ppcHeadAt 3510 12 (fi22T2Xs.drop 4) (fi22T2Rs.drop 4) (fi22T2Cjs.drop 4)
    (fi22T2Bs.drop 4) = true := by
  quickRfl

theorem kH5 : ppcHeadAt 3510 12 (fi22T2Xs.drop 5) (fi22T2Rs.drop 5) (fi22T2Cjs.drop 5)
    (fi22T2Bs.drop 5) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
