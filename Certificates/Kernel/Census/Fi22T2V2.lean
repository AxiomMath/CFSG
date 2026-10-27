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

theorem kV16 : (pinvRest 3510 12 fi22T2Xs 65536 (fi22T2Im.filter fun m => Nat.ble 65536 m) fi22T2Wt16 ==
    some (fi22T2Im.filter fun m => Nat.ble 69632 m)) = true := by
  quickRfl

theorem kV17 : (pinvRest 3510 12 fi22T2Xs 69632 (fi22T2Im.filter fun m => Nat.ble 69632 m) fi22T2Wt17 ==
    some (fi22T2Im.filter fun m => Nat.ble 73728 m)) = true := by
  quickRfl

theorem kV18 : (pinvRest 3510 12 fi22T2Xs 73728 (fi22T2Im.filter fun m => Nat.ble 73728 m) fi22T2Wt18 ==
    some (fi22T2Im.filter fun m => Nat.ble 77824 m)) = true := by
  quickRfl

theorem kV19 : (pinvRest 3510 12 fi22T2Xs 77824 (fi22T2Im.filter fun m => Nat.ble 77824 m) fi22T2Wt19 ==
    some (fi22T2Im.filter fun m => Nat.ble 81920 m)) = true := by
  quickRfl

theorem kV20 : (pinvRest 3510 12 fi22T2Xs 81920 (fi22T2Im.filter fun m => Nat.ble 81920 m) fi22T2Wt20 ==
    some (fi22T2Im.filter fun m => Nat.ble 86016 m)) = true := by
  quickRfl

theorem kV21 : (pinvRest 3510 12 fi22T2Xs 86016 (fi22T2Im.filter fun m => Nat.ble 86016 m) fi22T2Wt21 ==
    some (fi22T2Im.filter fun m => Nat.ble 90112 m)) = true := by
  quickRfl

theorem kV22 : (pinvRest 3510 12 fi22T2Xs 90112 (fi22T2Im.filter fun m => Nat.ble 90112 m) fi22T2Wt22 ==
    some (fi22T2Im.filter fun m => Nat.ble 94208 m)) = true := by
  quickRfl

theorem kV23 : (pinvRest 3510 12 fi22T2Xs 94208 (fi22T2Im.filter fun m => Nat.ble 94208 m) fi22T2Wt23 ==
    some (fi22T2Im.filter fun m => Nat.ble 98304 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
