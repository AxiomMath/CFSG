module

public import Certificates.Data.E4MoveSp6
import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound
import Certificates.Kernel.PermCent.K550105
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6E CFSG.Sporadic.Schreier

namespace Certificates

open CertificateChecks

private theorem move_eq550105 : moveCheck () = moveC := by
  rw [moveCheck.eq_1, moveElems.eq_1, enumerationTab_eq, E2_ev, moveC.eq_1, moveT.eq_1]
  simp only [moveInvs.eq_1, moveThrees.eq_1, tab_eq, rep2_ev, rho_ev, jay_ev, List.filter_map,
    List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev, ne_eq,
    Bool.decide_and, decide_not, decide_ev_eq]

theorem certificate550105 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.moveCheck () = true := by
  rw [move_eq550105]
  exact KernelPermCent.k550105

end Certificates
