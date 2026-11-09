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
import Certificates.Kernel.KSU38R.NoV4
import Certificates.Kernel.KSU38R.DCyc

public section

namespace CertificateChecks.Batch36922

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open KSU38R CertificateChecks.KSU38RK

private theorem exp_0n : expN2 = true := by decide +kernel

private theorem exp_0 : expN = true := expN_of exp_0n

private theorem nov4_1n : noV4N2 = true := by decide +kernel

private theorem nov4_1 : noV4N = true := noV4N_of nov4_1n

private theorem rep_2 : repCheck () = true := by decide +kernel

private theorem e0_3 : e0Check () = true := by decide +kernel

private theorem reg_4 : regCheck () = true := by decide +kernel

private theorem d_5n : dN2 = true := by decide +kernel

private theorem d_5 : dN = true := dN_of d_5n

private theorem check_0 : KSU38R.u38RCheck () = true := by
  simp only [u38RCheck, expCheck_eq, exp_0, noV4Check_eq, nov4_1, rep_2, e0_3, reg_4, dCheck_eq, d_5,
    Bool.and_self]

end CertificateChecks.Batch36922

namespace Certificates

open CertificateChecks

theorem certificate36922 : KSU38R.u38RCheck () = true := CertificateChecks.Batch36922.check_0

end Certificates
