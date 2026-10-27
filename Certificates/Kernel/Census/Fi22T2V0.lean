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

theorem kV0 : (pinvRest 3510 12 fi22T2Xs 0 (fi22T2Im.filter fun m => Nat.ble 0 m) fi22T2Wt0 ==
    some (fi22T2Im.filter fun m => Nat.ble 4096 m)) = true := by
  quickRfl

theorem kV1 : (pinvRest 3510 12 fi22T2Xs 4096 (fi22T2Im.filter fun m => Nat.ble 4096 m) fi22T2Wt1 ==
    some (fi22T2Im.filter fun m => Nat.ble 8192 m)) = true := by
  quickRfl

theorem kV2 : (pinvRest 3510 12 fi22T2Xs 8192 (fi22T2Im.filter fun m => Nat.ble 8192 m) fi22T2Wt2 ==
    some (fi22T2Im.filter fun m => Nat.ble 12288 m)) = true := by
  quickRfl

theorem kV3 : (pinvRest 3510 12 fi22T2Xs 12288 (fi22T2Im.filter fun m => Nat.ble 12288 m) fi22T2Wt3 ==
    some (fi22T2Im.filter fun m => Nat.ble 16384 m)) = true := by
  quickRfl

theorem kV4 : (pinvRest 3510 12 fi22T2Xs 16384 (fi22T2Im.filter fun m => Nat.ble 16384 m) fi22T2Wt4 ==
    some (fi22T2Im.filter fun m => Nat.ble 20480 m)) = true := by
  quickRfl

theorem kV5 : (pinvRest 3510 12 fi22T2Xs 20480 (fi22T2Im.filter fun m => Nat.ble 20480 m) fi22T2Wt5 ==
    some (fi22T2Im.filter fun m => Nat.ble 24576 m)) = true := by
  quickRfl

theorem kV6 : (pinvRest 3510 12 fi22T2Xs 24576 (fi22T2Im.filter fun m => Nat.ble 24576 m) fi22T2Wt6 ==
    some (fi22T2Im.filter fun m => Nat.ble 28672 m)) = true := by
  quickRfl

theorem kV7 : (pinvRest 3510 12 fi22T2Xs 28672 (fi22T2Im.filter fun m => Nat.ble 28672 m) fi22T2Wt7 ==
    some (fi22T2Im.filter fun m => Nat.ble 32768 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T2

end
