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

theorem kV48 : (pinvRest 3510 12 fi22T1Xs 196608 (fi22T1Im.filter fun m => Nat.ble 196608 m) fi22T1Wt48 ==
    some (fi22T1Im.filter fun m => Nat.ble 200704 m)) = true := by
  quickRfl

theorem kV49 : (pinvRest 3510 12 fi22T1Xs 200704 (fi22T1Im.filter fun m => Nat.ble 200704 m) fi22T1Wt49 ==
    some (fi22T1Im.filter fun m => Nat.ble 204800 m)) = true := by
  quickRfl

theorem kV50 : (pinvRest 3510 12 fi22T1Xs 204800 (fi22T1Im.filter fun m => Nat.ble 204800 m) fi22T1Wt50 ==
    some (fi22T1Im.filter fun m => Nat.ble 208896 m)) = true := by
  quickRfl

theorem kV51 : (pinvRest 3510 12 fi22T1Xs 208896 (fi22T1Im.filter fun m => Nat.ble 208896 m) fi22T1Wt51 ==
    some (fi22T1Im.filter fun m => Nat.ble 212992 m)) = true := by
  quickRfl

theorem kV52 : (pinvRest 3510 12 fi22T1Xs 212992 (fi22T1Im.filter fun m => Nat.ble 212992 m) fi22T1Wt52 ==
    some (fi22T1Im.filter fun m => Nat.ble 217088 m)) = true := by
  quickRfl

theorem kV53 : (pinvRest 3510 12 fi22T1Xs 217088 (fi22T1Im.filter fun m => Nat.ble 217088 m) fi22T1Wt53 ==
    some (fi22T1Im.filter fun m => Nat.ble 221184 m)) = true := by
  quickRfl

theorem kV54 : (pinvRest 3510 12 fi22T1Xs 221184 (fi22T1Im.filter fun m => Nat.ble 221184 m) fi22T1Wt54 ==
    some (fi22T1Im.filter fun m => Nat.ble 225280 m)) = true := by
  quickRfl

theorem kV55 : (pinvRest 3510 12 fi22T1Xs 225280 (fi22T1Im.filter fun m => Nat.ble 225280 m) fi22T1Wt55 ==
    some (fi22T1Im.filter fun m => Nat.ble 229376 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
