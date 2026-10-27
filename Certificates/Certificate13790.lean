module

public import CFSG.Sporadic.Schreier.ONEightNormalizersCheck
import Certificates.Kernel.Sporadic.ONEN.Check
import Certificates.Kernel.Sporadic.ONEN.Sound

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.ONEN

theorem certificate13790 : CFSG.ONSchreier.onEightNormalizersCheck = true := by
  refine sound13790 ?_ ?_ ch13790D_ok ?_
  · rintro x (rfl | rfl | rfl)
    exacts [ch13790A_0, ch13790A_1, ch13790A_2]
  · intro j hj
    interval_cases j
    exacts [ch13790E_0, ch13790E_1]
  · intro i hi
    interval_cases i
    exacts [ch13790N_0, ch13790N_1, ch13790N_2, ch13790N_3]

end Certificates
