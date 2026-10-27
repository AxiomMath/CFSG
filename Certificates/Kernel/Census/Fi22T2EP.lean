module

public import Certificates.Kernel.Census.Fi22RDefsT2
public import Certificates.Data.Kernel.Census.PackedRootP
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkT2R
import Certificates.Kernel.Census.Fi22PkT2A
import Certificates.Kernel.Census.Fi22PkT2W
import Certificates.Kernel.Census.Fi22PkT2K
import Certificates.Kernel.Census.Fi22PkU
import Certificates.Data.Kernel.Census.PackedL
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

theorem kEP0 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 0 512 = true := by quickRfl
theorem kEP1 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 512 512 = true := by quickRfl
theorem kEP2 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 1024 512 = true := by quickRfl
theorem kEP3 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 1536 512 = true := by quickRfl
theorem kEP4 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 2048 512 = true := by quickRfl
theorem kEP5 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 2560 512 = true := by quickRfl
theorem kEP6 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 3072 512 = true := by quickRfl
theorem kEP7 : pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root 3584 191 = true := by quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
