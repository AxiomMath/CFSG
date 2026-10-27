module

public import Certificates.Data.E4SigmaSp6
import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound
import Certificates.Kernel.PermCent.K55117
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6E CFSG.Certificates.Kernel.PkCV.Sp6B CFSG.Sporadic.Schreier

namespace Certificates

open CertificateChecks

private theorem sig_eq55117 : sigCheck () = sigC := by
  rw [sigCheck.eq_1, twin_ev, rho_ev, jay_ev, L1_ev, E2_ev, sigC.eq_1, sigT.eq_1]
  simp only [map_tab, List.all_map, List.any_map, Function.comp_def, tab_eq, sigStep.eq_1, ev_mul',
    ev_inv', one_eq_ev, decide_ev_eq]

theorem certificate55117 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.sigCheck () = true := by
  rw [sig_eq55117]
  exact KernelPermCent.k55117

end Certificates
