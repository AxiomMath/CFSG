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

theorem kV32 : (pinvRest 3510 12 fi22T1Xs 131072 (fi22T1Im.filter fun m => Nat.ble 131072 m) fi22T1Wt32 ==
    some (fi22T1Im.filter fun m => Nat.ble 135168 m)) = true := by
  quickRfl

theorem kV33 : (pinvRest 3510 12 fi22T1Xs 135168 (fi22T1Im.filter fun m => Nat.ble 135168 m) fi22T1Wt33 ==
    some (fi22T1Im.filter fun m => Nat.ble 139264 m)) = true := by
  quickRfl

theorem kV34 : (pinvRest 3510 12 fi22T1Xs 139264 (fi22T1Im.filter fun m => Nat.ble 139264 m) fi22T1Wt34 ==
    some (fi22T1Im.filter fun m => Nat.ble 143360 m)) = true := by
  quickRfl

theorem kV35 : (pinvRest 3510 12 fi22T1Xs 143360 (fi22T1Im.filter fun m => Nat.ble 143360 m) fi22T1Wt35 ==
    some (fi22T1Im.filter fun m => Nat.ble 147456 m)) = true := by
  quickRfl

theorem kV36 : (pinvRest 3510 12 fi22T1Xs 147456 (fi22T1Im.filter fun m => Nat.ble 147456 m) fi22T1Wt36 ==
    some (fi22T1Im.filter fun m => Nat.ble 151552 m)) = true := by
  quickRfl

theorem kV37 : (pinvRest 3510 12 fi22T1Xs 151552 (fi22T1Im.filter fun m => Nat.ble 151552 m) fi22T1Wt37 ==
    some (fi22T1Im.filter fun m => Nat.ble 155648 m)) = true := by
  quickRfl

theorem kV38 : (pinvRest 3510 12 fi22T1Xs 155648 (fi22T1Im.filter fun m => Nat.ble 155648 m) fi22T1Wt38 ==
    some (fi22T1Im.filter fun m => Nat.ble 159744 m)) = true := by
  quickRfl

theorem kV39 : (pinvRest 3510 12 fi22T1Xs 159744 (fi22T1Im.filter fun m => Nat.ble 159744 m) fi22T1Wt39 ==
    some (fi22T1Im.filter fun m => Nat.ble 163840 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
