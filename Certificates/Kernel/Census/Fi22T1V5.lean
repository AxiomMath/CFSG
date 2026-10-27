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

theorem kV40 : (pinvRest 3510 12 fi22T1Xs 163840 (fi22T1Im.filter fun m => Nat.ble 163840 m) fi22T1Wt40 ==
    some (fi22T1Im.filter fun m => Nat.ble 167936 m)) = true := by
  quickRfl

theorem kV41 : (pinvRest 3510 12 fi22T1Xs 167936 (fi22T1Im.filter fun m => Nat.ble 167936 m) fi22T1Wt41 ==
    some (fi22T1Im.filter fun m => Nat.ble 172032 m)) = true := by
  quickRfl

theorem kV42 : (pinvRest 3510 12 fi22T1Xs 172032 (fi22T1Im.filter fun m => Nat.ble 172032 m) fi22T1Wt42 ==
    some (fi22T1Im.filter fun m => Nat.ble 176128 m)) = true := by
  quickRfl

theorem kV43 : (pinvRest 3510 12 fi22T1Xs 176128 (fi22T1Im.filter fun m => Nat.ble 176128 m) fi22T1Wt43 ==
    some (fi22T1Im.filter fun m => Nat.ble 180224 m)) = true := by
  quickRfl

theorem kV44 : (pinvRest 3510 12 fi22T1Xs 180224 (fi22T1Im.filter fun m => Nat.ble 180224 m) fi22T1Wt44 ==
    some (fi22T1Im.filter fun m => Nat.ble 184320 m)) = true := by
  quickRfl

theorem kV45 : (pinvRest 3510 12 fi22T1Xs 184320 (fi22T1Im.filter fun m => Nat.ble 184320 m) fi22T1Wt45 ==
    some (fi22T1Im.filter fun m => Nat.ble 188416 m)) = true := by
  quickRfl

theorem kV46 : (pinvRest 3510 12 fi22T1Xs 188416 (fi22T1Im.filter fun m => Nat.ble 188416 m) fi22T1Wt46 ==
    some (fi22T1Im.filter fun m => Nat.ble 192512 m)) = true := by
  quickRfl

theorem kV47 : (pinvRest 3510 12 fi22T1Xs 192512 (fi22T1Im.filter fun m => Nat.ble 192512 m) fi22T1Wt47 ==
    some (fi22T1Im.filter fun m => Nat.ble 196608 m)) = true := by
  quickRfl

end CertificateChecks.KernelCensus.Fi22K.T1

end
