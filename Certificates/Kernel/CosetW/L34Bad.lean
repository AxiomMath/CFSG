module

public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import Certificates.Data.Kernel.CosetW.EnumW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

@[expose] def l34BadCheck (I : List (Fin 12)) : Bool := I.all fun i => [2, 3].all fun k =>
  (decide (IsGood i) && k == 3) ||
    checkW (mkParamsW (2 * 5) (invArrW 5)
      (codes (amalRels ++ [(List.replicate k (word "s" ++ word (repStr i))).flatten]))
      (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 1

theorem l34Bad_join {l1 l2 : List (Fin 12)} (h1 : l34BadCheck l1 = true)
    (h2 : l34BadCheck l2 = true) : l34BadCheck (l1 ++ l2) = true := by
  unfold l34BadCheck at *
  rw [List.all_append, h1, h2]
  rfl

set_option maxHeartbeats 0 in
theorem l34Bad_i0 : l34BadCheck [0] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i1 : l34BadCheck [1] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i2 : l34BadCheck [2] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i3 : l34BadCheck [3] = true := by quickRfl

theorem l34Bad_checkW_a : l34BadCheck [0, 1, 2, 3] = true :=
  l34Bad_join (l1 := [0]) l34Bad_i0 (l34Bad_join (l1 := [1]) l34Bad_i1
    (l34Bad_join (l1 := [2]) l34Bad_i2 l34Bad_i3))

set_option maxHeartbeats 0 in
theorem l34Bad_i4 : l34BadCheck [4] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i5 : l34BadCheck [5] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i6 : l34BadCheck [6] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i7 : l34BadCheck [7] = true := by quickRfl

theorem l34Bad_checkW_b : l34BadCheck [4, 5, 6, 7] = true :=
  l34Bad_join (l1 := [4]) l34Bad_i4 (l34Bad_join (l1 := [5]) l34Bad_i5
    (l34Bad_join (l1 := [6]) l34Bad_i6 l34Bad_i7))

set_option maxHeartbeats 0 in
theorem l34Bad_i8 : l34BadCheck [8] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i9 : l34BadCheck [9] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i10 : l34BadCheck [10] = true := by quickRfl

set_option maxHeartbeats 0 in
theorem l34Bad_i11 : l34BadCheck [11] = true := by quickRfl

theorem l34Bad_checkW_c : l34BadCheck [8, 9, 10, 11] = true :=
  l34Bad_join (l1 := [8]) l34Bad_i8 (l34Bad_join (l1 := [9]) l34Bad_i9
    (l34Bad_join (l1 := [10]) l34Bad_i10 l34Bad_i11))

end CertificateChecks.CosetW
