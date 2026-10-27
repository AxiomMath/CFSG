module

public import CFSG.Monster.B.TwoA.Census.CosetSquares
meta import CFSG.Monster.B.TwoA.Census.CosetSquares
meta import CFSG.Monster.B.Rep4371.Model
meta import CFSG.Monster.B.TwoA.Census.MonoCert
import CFSG.Monster.B.Cbar.GenData

public section

open CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch3053

open CFSG.Monster.B.TwoA.Census

private theorem alpha_check_0 : alphaN 1 (false, 70, 5) = (true, 70, 186) := by
  decide +kernel

end CertificateChecks.Batch3053

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census in
theorem certificate3053 : alphaN 1 (false, 70, 5) = (true, 70, 186) := by
  exact CertificateChecks.Batch3053.alpha_check_0

end Certificates
