module

public import Certificates.Data.OmegaCentK
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K442003
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.P45T Certificates.OmegaCentK

namespace Certificates

private theorem centK_eq : check () = centKC := by
  unfold check centL oddL centChk centKC
  conv_lhs => rw [eq_ev_cOf (Certificates.P43Twin.tA ()), elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.filter_map, List.all_map, Function.comp_def, ev_mul', ev_pow', one_eq_ev,
    decide_ev_eq, comm_fast, pow_fast]

theorem certificate442003 : OmegaCentK.check () = true := by
  rw [centK_eq]
  exact k442003

end Certificates
