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

theorem kV56 : (pinvRest 3510 12 fi22T1Xs 229376 (fi22T1Im.filter fun m => Nat.ble 229376 m) fi22T1Wt56 ==
    some (fi22T1Im.filter fun m => Nat.ble 233472 m)) = true := by
  quickRfl

theorem kV57 : (pinvRest 3510 12 fi22T1Xs 233472 (fi22T1Im.filter fun m => Nat.ble 233472 m) fi22T1Wt57 ==
    some (fi22T1Im.filter fun m => Nat.ble 237568 m)) = true := by
  quickRfl

theorem kV58 : (pinvRest 3510 12 fi22T1Xs 237568 (fi22T1Im.filter fun m => Nat.ble 237568 m) fi22T1Wt58 ==
    some (fi22T1Im.filter fun m => Nat.ble 241664 m)) = true := by
  quickRfl

theorem kV59 : (pinvRest 3510 12 fi22T1Xs 241664 (fi22T1Im.filter fun m => Nat.ble 241664 m) fi22T1Wt59 ==
    some (fi22T1Im.filter fun m => Nat.ble 245760 m)) = true := by
  quickRfl

theorem kV60 : (pinvRest 3510 12 fi22T1Xs 245760 (fi22T1Im.filter fun m => Nat.ble 245760 m) fi22T1Wt60 ==
    some (fi22T1Im.filter fun m => Nat.ble 249856 m)) = true := by
  quickRfl

theorem kV61 : (pinvRest 3510 12 fi22T1Xs 249856 (fi22T1Im.filter fun m => Nat.ble 249856 m) fi22T1Wt61 ==
    some (fi22T1Im.filter fun m => Nat.ble 253952 m)) = true := by
  quickRfl

theorem kV62 : (pinvRest 3510 12 fi22T1Xs 253952 (fi22T1Im.filter fun m => Nat.ble 253952 m) fi22T1Wt62 ==
    some (fi22T1Im.filter fun m => Nat.ble 258048 m)) = true := by
  quickRfl

theorem kV63 : (pinvRest 3510 12 fi22T1Xs 258048 (fi22T1Im.filter fun m => Nat.ble 258048 m) fi22T1Wt63 ==
    some (fi22T1Im.filter fun m => Nat.ble 262144 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
