module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12QuadCheck

public section

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

namespace CertificateChecks.Batch17280

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

private theorem hj_quad_four_check_0 : hjQuadFourCheck = true := by
  decide +kernel

end CertificateChecks.Batch17280

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 in
theorem certificate17280 : hjQuadFourCheck = true :=
  CertificateChecks.Batch17280.hj_quad_four_check_0

end Certificates
