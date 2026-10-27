module

public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

theorem l34Good2_checkW : checkW (mkParamsW (2 * 5) (invArrW 5)
    (codes (amalRels ++ [(List.replicate 3 (word "s" ++ word (repStr 2))).flatten]))
    (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 21 = true := by
  decide +kernel

theorem l34Good5_checkW : checkW (mkParamsW (2 * 5) (invArrW 5)
    (codes (amalRels ++ [(List.replicate 3 (word "s" ++ word (repStr 5))).flatten]))
    (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 21 = true := by
  decide +kernel

theorem l34Good7_checkW : checkW (mkParamsW (2 * 5) (invArrW 5)
    (codes (amalRels ++ [(List.replicate 3 (word "s" ++ word (repStr 7))).flatten]))
    (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 21 = true := by
  decide +kernel

end CertificateChecks.CosetW
