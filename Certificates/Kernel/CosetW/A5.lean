module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5Inputs
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

theorem a5_checkW : checkW (mkParamsW (2 * 2) (invArrW 2) (codes a5Rels)
    (codes ((subsetOf 2 []).map fun x => [(x, true)]))) 100000 60 = true := by
  decide +kernel

end CertificateChecks.CosetW
