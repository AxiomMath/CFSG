module

public import Certificates.Data.K426J3
public import Certificates.Data.Kernel.CosetW.EnumW

public section

set_option maxRecDepth 400000

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.CosetTable CFSG.Certificates.CosetEnumeration

namespace CertificateChecks.CosetW

set_option maxHeartbeats 0 in
theorem j3tLift_checkW :
    checkW (mkParamsW (2 * 2) (invArrW 2) (codes j3tLiftRels) [[2]]) 2000 90 = true := by
  decide +kernel

end CertificateChecks.CosetW
