module

public import Certificates.Data.E4QuatSp6Good
import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound
import Certificates.Kernel.PermCent.K55109
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6E
  CFSG.Certificates.Kernel.PkCV.Sp6B

namespace Certificates

open CertificateChecks

private theorem ng_eq55109 : ngCheck () = ngC := by
  rw [ngCheck.eq_1, L0_ev, rho_ev, jay_ev, ngWit_ev, E2_ev, ngC.eq_1, ngT.eq_1]
  simp only [List.all_map, Function.comp_def, ngBad.eq_1, norms_ev, ev_mul', ev_inv', ev_pow',
    one_eq_ev, decide_ev_eq]

theorem certificate55109 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.ngCheck () = true := by
  rw [ng_eq55109]
  exact KernelPermCent.k55109

end Certificates
