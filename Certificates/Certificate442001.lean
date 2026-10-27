module

public import Certificates.Data.OmegaT0
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K442001S
import Certificates.Kernel.PermCent.K442001N
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.P45T Certificates.OmegaT0

namespace Certificates

private theorem sylow_eq : sylowChk () = sylowC := by
  unfold sylowChk sylowC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.filter_map, List.length_map, List.all_map, Function.comp_def, ev_mul',
    decide_ev_eq, decide_mem_map_ev, comm_fast]

private theorem n7_eq : n7Chk () = n7C := by
  unfold n7Chk n7C coverOK cntCent coverC cntCentC
  conv_lhs => rw [eq_ev_cOf (z0 ()), eq_ev_cOf (yB ()), eq_ev_cOf (za ()), eq_ev_cOf (zb ()),
    eq_ev_cOf (ya ()), eq_ev_cOf (yb ()), elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.filter_map, List.length_map, List.all_map, List.any_map, List.any_cons,
    List.any_nil, Function.comp_def, ev_mul', ev_inv', one_eq_ev, decide_ev_eq,
    decide_mem_map_ev, comm_fast, conj_fast, sq_fast, Bool.decide_and, ne_eq, decide_not,
    Bool.or_false]

theorem certificate442001 : OmegaT0.check () = true := by
  rw [check.eq_1, sylow_eq, n7_eq, k442001S, k442001N]
  rfl

end Certificates
