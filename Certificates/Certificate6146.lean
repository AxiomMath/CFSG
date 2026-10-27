
module

public import CFSG.LocalAnalysis.OddStandard.ONanDefs
import Certificates.Kernel.ONanNormal.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec in
theorem certificate6146 : ∀ S : Subgroup CModel, IsPGroup 2 S → S.Normal → Nat.card S ≤ 4 := ONanNormal.normal2

end Certificates
