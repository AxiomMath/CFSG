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

theorem kM0a : (pvalid 3510 12 fi22T1Root.x && pinvol 3510 12 fi22T1Root.x && inWK fi22T1Root.x) = true := by
  quickRfl

theorem kM0b : (Nat.beq fi22T1Root.xi.length fi22T1Root.xs.length &&
    (fi22T1Root.xs.zip fi22T1Root.xi).all (fun gi => Nat.beq (pc 3510 12 gi.2 gi.1) (pid 3510 12))) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
