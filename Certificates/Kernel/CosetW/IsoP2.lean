module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.Quasithin.L34Amalgam CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

set_option maxHeartbeats 0 in
theorem isoP2_checkW : checkW (mkParamsW (2 * 5) (invArrW 5) (codes relsP2)
    (codes ((subsetOf 5 [0, 2]).map fun x => [(x, true)]))) 100000 80 = true := by
  decide +kernel

theorem isoP2Sub_checkW :
    checkW (mkParamsW (2 * (subsetOf 5 [0, 2]).length) (invArrW (subsetOf 5 [0, 2]).length)
      (codes (restrictWords (subsetOf 5 [0, 2]) relsP2))
      (codes ((subsetOf (subsetOf 5 [0, 2]).length []).map fun x => [(x, true)])))
      100000 12 = true := by
  decide +kernel

end CertificateChecks.CosetW
