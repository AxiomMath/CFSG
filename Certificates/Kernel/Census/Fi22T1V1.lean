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

theorem kV8 : (pinvRest 3510 12 fi22T1Xs 32768 (fi22T1Im.filter fun m => Nat.ble 32768 m) fi22T1Wt8 ==
    some (fi22T1Im.filter fun m => Nat.ble 36864 m)) = true := by
  quickRfl

theorem kV9 : (pinvRest 3510 12 fi22T1Xs 36864 (fi22T1Im.filter fun m => Nat.ble 36864 m) fi22T1Wt9 ==
    some (fi22T1Im.filter fun m => Nat.ble 40960 m)) = true := by
  quickRfl

theorem kV10 : (pinvRest 3510 12 fi22T1Xs 40960 (fi22T1Im.filter fun m => Nat.ble 40960 m) fi22T1Wt10 ==
    some (fi22T1Im.filter fun m => Nat.ble 45056 m)) = true := by
  quickRfl

theorem kV11 : (pinvRest 3510 12 fi22T1Xs 45056 (fi22T1Im.filter fun m => Nat.ble 45056 m) fi22T1Wt11 ==
    some (fi22T1Im.filter fun m => Nat.ble 49152 m)) = true := by
  quickRfl

theorem kV12 : (pinvRest 3510 12 fi22T1Xs 49152 (fi22T1Im.filter fun m => Nat.ble 49152 m) fi22T1Wt12 ==
    some (fi22T1Im.filter fun m => Nat.ble 53248 m)) = true := by
  quickRfl

theorem kV13 : (pinvRest 3510 12 fi22T1Xs 53248 (fi22T1Im.filter fun m => Nat.ble 53248 m) fi22T1Wt13 ==
    some (fi22T1Im.filter fun m => Nat.ble 57344 m)) = true := by
  quickRfl

theorem kV14 : (pinvRest 3510 12 fi22T1Xs 57344 (fi22T1Im.filter fun m => Nat.ble 57344 m) fi22T1Wt14 ==
    some (fi22T1Im.filter fun m => Nat.ble 61440 m)) = true := by
  quickRfl

theorem kV15 : (pinvRest 3510 12 fi22T1Xs 61440 (fi22T1Im.filter fun m => Nat.ble 61440 m) fi22T1Wt15 ==
    some (fi22T1Im.filter fun m => Nat.ble 65536 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
