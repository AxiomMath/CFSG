module

public import Certificates.Data.SmithB45ExcM11Check
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K260380
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV
  CFSG.Quasithin.B45Exc CFSG.QuasithinUnique.Setup.X1

namespace Certificates

open CertificateChecks

private theorem o4_eq260380 : m11O4Check = M11B.o4C := by
  have o2 : ∀ g : CV 11, orderIs g 2 = orderIsP g 2 [2] :=
    fun g => orderIs_eq_P g 2 [2] (by norm_num) (by decide) (by decide)
  have o4 : ∀ g : CV 11, orderIs g 4 = orderIsP g 4 [2] :=
    fun g => orderIs_eq_P g 4 [2] (by norm_num) (by decide) (by decide)
  have o8 : ∀ g : CV 11, orderIs g 8 = orderIsP g 8 [2] :=
    fun g => orderIs_eq_P g 8 [2] (by norm_num) (by decide) (by decide)
  have hE : m11Elements = (elemsC m11Certificate).map ev := elemsT_eq_elemsC m11Certificate
  rw [m11O4Check.eq_1, m11Invs.eq_1, hE, eq_ev_cOf m11gA, M11B.o4C.eq_1, M11B.E.eq_1,
    M11B.A.eq_1, List.filter_map, List.all_map]
  simp only [Function.comp_def, List.any_map, ev_mul', ev_inv', orderIs_ev, beq_ev, beq_cv, o2,
    o4, o8]

open CFSG.Quasithin.B45Exc in
theorem certificate260380 : m11O4Check = true := by
  rw [o4_eq260380]
  exact KernelPermCent.k260380

end Certificates
