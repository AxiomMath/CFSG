module

public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

@[expose] def l34BadCheck (I : List (Fin 12)) : Bool := I.all fun i => [2, 3].all fun k =>
  (decide (IsGood i) && k == 3) ||
    checkW (mkParamsW (2 * 5) (invArrW 5)
      (codes (amalRels ++ [(List.replicate k (word "s" ++ word (repStr i))).flatten]))
      (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 1

set_option maxHeartbeats 0 in
theorem l34Bad_checkW_a : l34BadCheck [0, 1, 2, 3] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem l34Bad_checkW_b : l34BadCheck [4, 5, 6, 7] = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem l34Bad_checkW_c : l34BadCheck [8, 9, 10, 11] = true := by
  decide +kernel

end CertificateChecks.CosetW
