module

public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

set_option maxHeartbeats 0 in
theorem l34P1_checkW :
    checkW (mkParamsW (2 * (subsetOf 5 [0, 1, 2, 3]).length)
      (invArrW (subsetOf 5 [0, 1, 2, 3]).length)
      (codes (restrictWords (subsetOf 5 [0, 1, 2, 3]) amalRels))
      (codes ((subsetOf (subsetOf 5 [0, 1, 2, 3]).length []).map fun x => [(x, true)])))
      100000 960 = true := by
  decide +kernel

theorem l34Extra_restrict : (([2, 5, 7] : List (Fin 12)).all fun i =>
    (restrictWords (subsetOf 5 [0, 1, 2, 3])
      [(List.replicate 3 (word "s" ++ word (repStr i))).flatten]).isEmpty) = true := by
  decide +kernel

theorem l34Subset_length : (subsetOf 5 [0, 1, 2, 3]).length = 4 := by
  decide +kernel

end CertificateChecks.CosetW
