module

public import Certificates.Data.E4Sp6Exp
import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound
import Certificates.Kernel.PermCent.K393004
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6E CFSG.Sporadic.Schreier

namespace Certificates

open CertificateChecks

private theorem centSq_eq393004 : centSqCheck () = centSqC := by
  rw [centSqCheck.eq_1, twin_ev, rho_ev, jay_ev, E2_ev, centSqC.eq_1, centSqT.eq_1]
  simp only [List.all_map, Function.comp_def, tab_eq, centSqStep.eq_1, ev_mul', ev_inv',
    one_eq_ev, decide_ev_eq]

theorem certificate393004 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.centSqCheck () = true := by
  rw [centSq_eq393004]
  exact KernelPermCent.k393004

end Certificates
