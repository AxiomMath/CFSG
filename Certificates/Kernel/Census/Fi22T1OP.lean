module

public import Certificates.Kernel.Census.Fi22RDefsT1
public import Certificates.Data.Kernel.Census.PackedRootP
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22PkT1R
import Certificates.Kernel.Census.Fi22PkT1A
import Certificates.Kernel.Census.Fi22PkT1W
import Certificates.Kernel.Census.Fi22PkT1K
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

namespace CertificateChecks.KernelCensus.Fi22K.T1

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22 CertificateChecks.KernelCensus.Fi22K

theorem kFit : fitsB fi22T1Root.ukc = true := by quickRfl

theorem kOP0 : pordBlkP 3510 12 fi22T1Root 0 512 = true := by quickRfl
theorem kOP1 : pordBlkP 3510 12 fi22T1Root 512 512 = true := by quickRfl
theorem kOP2 : pordBlkP 3510 12 fi22T1Root 1024 512 = true := by quickRfl
theorem kOP3 : pordBlkP 3510 12 fi22T1Root 1536 512 = true := by quickRfl
theorem kOP4 : pordBlkP 3510 12 fi22T1Root 2048 512 = true := by quickRfl
theorem kOP5 : pordBlkP 3510 12 fi22T1Root 2560 512 = true := by quickRfl
theorem kOP6 : pordBlkP 3510 12 fi22T1Root 3072 512 = true := by quickRfl
theorem kOP7 : pordBlkP 3510 12 fi22T1Root 3584 512 = true := by quickRfl
theorem kOP8 : pordBlkP 3510 12 fi22T1Root 4096 512 = true := by quickRfl
theorem kOP9 : pordBlkP 3510 12 fi22T1Root 4608 512 = true := by quickRfl
theorem kOP10 : pordBlkP 3510 12 fi22T1Root 5120 512 = true := by quickRfl
theorem kOP11 : pordBlkP 3510 12 fi22T1Root 5632 510 = true := by quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
