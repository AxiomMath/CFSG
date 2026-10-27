module

public import Certificates.Data.E189E4tSp6
import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound
import Certificates.Kernel.PermCent.K294001

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6E CFSG.Certificates.Kernel.PkCV.Sp6B CFSG.Sporadic.Schreier

namespace Certificates

open CertificateChecks

private theorem t_eq294001 : tcheck () = tC := by
  rw [tcheck.eq_1, L0_ev, tab_eq, rep2_ev, rho_ev, jay_ev, ws_ev, tCheck_ev, tC.eq_1]

theorem certificate294001 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.tcheck () = true := by
  rw [t_eq294001]
  exact KernelPermCent.k294001

end Certificates
