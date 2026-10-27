module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamA6Inputs
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K5159
public import CFSG.GH74.KGroups.A6Inputs
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.GH74.GLS.C3.Layer1.EndN.A6
  CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

private theorem a6_eq5159 : a6check (elemsT QA) (elemsT QP) = A6B.a6C := by
  have o1 : ∀ g : CV 10, orderIs g 1 = orderIsP g 1 [] :=
    fun g => orderIs_eq_P g 1 [] (by norm_num) (by decide) (by decide)
  have o2 : ∀ g : CV 10, orderIs g 2 = orderIsP g 2 [2] :=
    fun g => orderIs_eq_P g 2 [2] (by norm_num) (by decide) (by decide)
  have o3 : ∀ g : CV 10, orderIs g 3 = orderIsP g 3 [3] :=
    fun g => orderIs_eq_P g 3 [3] (by norm_num) (by decide) (by decide)
  have o4 : ∀ g : CV 10, orderIs g 4 = orderIsP g 4 [2] :=
    fun g => orderIs_eq_P g 4 [2] (by norm_num) (by decide) (by decide)
  have o5 : ∀ g : CV 10, orderIs g 5 = orderIsP g 5 [5] :=
    fun g => orderIs_eq_P g 5 [5] (by norm_num) (by decide) (by decide)
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, a6check.eq_1, A6B.a6C.eq_1]
  simp only [wit.eq_1, evenOrd.eq_1, A6B.witC.eq_1, A6B.evenOrdC.eq_1, Function.comp_def,
    List.all_map, List.any_map, List.filter_map, ev_mul', ev_inv', orderIs_ev, one_eq_ev, ne_eq,
    ev_eq_iff, decide_ev_eq, o1, o2, o3, o4, o5]

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.GH74.GLS.C3.Layer1.EndN.A6 in
theorem certificate5159 : a6check (elemsT QA) (elemsT QP) = true := by
  rw [a6_eq5159]
  exact KernelPermCent.k5159

end Certificates
