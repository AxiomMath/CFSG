module

public import Certificates.Data.KSU38R.Check
import all CFSG.LieType.SeitzGeneration.HeisSmallCheck
import all CFSG.LieType.SeitzGeneration.HeisSmallModel
import all CFSG.LieType.SeitzGeneration.HeisSmallData8
import all CFSG.LieType.SeitzGeneration.OuterSmallCheck
import all CFSG.LieType.SeitzGeneration.OuterSmallData8
import all Certificates.Data.HuppertU38F.Check
import all Certificates.Data.HuppertU38F.Data
import all Certificates.Data.KSU38R.Check

public section

namespace CertificateChecks.Batch36922

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem check_0 : KSU38R.u38RCheck () = true := by decide +kernel

end CertificateChecks.Batch36922

namespace Certificates

open CertificateChecks

theorem certificate36922 : KSU38R.u38RCheck () = true := CertificateChecks.Batch36922.check_0

end Certificates
