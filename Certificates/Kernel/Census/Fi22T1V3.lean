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

theorem kV24 : (pinvRest 3510 12 fi22T1Xs 98304 (fi22T1Im.filter fun m => Nat.ble 98304 m) fi22T1Wt24 ==
    some (fi22T1Im.filter fun m => Nat.ble 102400 m)) = true := by
  quickRfl

theorem kV25 : (pinvRest 3510 12 fi22T1Xs 102400 (fi22T1Im.filter fun m => Nat.ble 102400 m) fi22T1Wt25 ==
    some (fi22T1Im.filter fun m => Nat.ble 106496 m)) = true := by
  quickRfl

theorem kV26 : (pinvRest 3510 12 fi22T1Xs 106496 (fi22T1Im.filter fun m => Nat.ble 106496 m) fi22T1Wt26 ==
    some (fi22T1Im.filter fun m => Nat.ble 110592 m)) = true := by
  quickRfl

theorem kV27 : (pinvRest 3510 12 fi22T1Xs 110592 (fi22T1Im.filter fun m => Nat.ble 110592 m) fi22T1Wt27 ==
    some (fi22T1Im.filter fun m => Nat.ble 114688 m)) = true := by
  quickRfl

theorem kV28 : (pinvRest 3510 12 fi22T1Xs 114688 (fi22T1Im.filter fun m => Nat.ble 114688 m) fi22T1Wt28 ==
    some (fi22T1Im.filter fun m => Nat.ble 118784 m)) = true := by
  quickRfl

theorem kV29 : (pinvRest 3510 12 fi22T1Xs 118784 (fi22T1Im.filter fun m => Nat.ble 118784 m) fi22T1Wt29 ==
    some (fi22T1Im.filter fun m => Nat.ble 122880 m)) = true := by
  quickRfl

theorem kV30 : (pinvRest 3510 12 fi22T1Xs 122880 (fi22T1Im.filter fun m => Nat.ble 122880 m) fi22T1Wt30 ==
    some (fi22T1Im.filter fun m => Nat.ble 126976 m)) = true := by
  quickRfl

theorem kV31 : (pinvRest 3510 12 fi22T1Xs 126976 (fi22T1Im.filter fun m => Nat.ble 126976 m) fi22T1Wt31 ==
    some (fi22T1Im.filter fun m => Nat.ble 131072 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
