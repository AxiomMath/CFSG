module

public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GH74.KGroups.ChecksE8
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K295133
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

private theorem noOrd_eq295133 : noOrdersCheck (elemsT QP) 14 21 = U33B.noOrdC := by
  have o14 : ∀ g : CV 28, orderIs g 14 = orderIsP g 14 [2, 7] :=
    fun g => orderIs_eq_P g 14 [2, 7] (by norm_num) (by decide) (by decide)
  have o21 : ∀ g : CV 28, orderIs g 21 = orderIsP g 21 [3, 7] :=
    fun g => orderIs_eq_P g 21 [3, 7] (by norm_num) (by decide) (by decide)
  rw [noOrdersCheck.eq_1, U33B.noOrdC.eq_1, elemsT_eq_elemsC, List.all_map]
  simp only [Function.comp_def, orderIs_ev, o14, o21]

private theorem e8_eq295133 : e8free (elemsT QP) = U33B.e8C := by
  rw [e8free.eq_1, U33B.e8C.eq_1, elemsT_eq_elemsC, List.all_map]
  simp only [e8at.eq_1, U33B.e8atC.eq_1, Function.comp_def, List.filter_map, List.all_map,
    List.mem_cons, List.not_mem_nil, or_false, ev_mul', ev_pow', one_eq_ev, ne_eq, ev_eq_iff]

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 in
theorem certificate295133 : (noOrdersCheck (elemsT QP) 14 21 = true) ∧ (e8free (elemsT QP) = true) := by
  rw [noOrd_eq295133, e8_eq295133]
  exact ⟨KernelPermCent.k295133_ord, KernelPermCent.k295133_e8⟩

end Certificates
