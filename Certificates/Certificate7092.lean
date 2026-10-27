module

public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
import Certificates.Kernel.Misc.Tits.Pi7092
import Certificates.Kernel.Sporadic.Tits.Order2264
import CFSG.Certificates.Kernel.Misc.TitsPiSound

public section

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor.Tits2264

namespace CertificateChecks.Batch7092

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor.Tits2264

private theorem pi_eq : CFSG.Quasithin.titsPiArr = unpack 1755 11 TitsPi.P :=
  CFSG.KC.TitsPi.cmpL_sound TitsPi.bind

private theorem T_le : T ≤ titsA := by
  unfold T
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact titsD_le_titsA (titsT_mem_titsD (i := j.val) (by omega))

private theorem t_mem : t ∈ titsA := by
  have e : t = titsGen 1 := by
    rw [titsGen, gen_eq (by norm_num)]
    rfl
  rw [e]
  exact titsGen_mem_titsA (by norm_num)

private theorem mem : permOfArr 1755 (unpack 1755 11 TitsPi.P) ∈ titsA := by
  have h1 := mem_T TitsPi.sift.1 TitsPi.sift.2
  rw [perm_mul TitsPi.perm TitsPi.permGI TitsPi.sift.2] at h1
  have hinv : permOfArr 1755 (unpack 1755 11 (GI 1)) = t⁻¹ :=
    (rep_of TitsPi.permGI).1.unique (rep_of (gperm 1 (by norm_num))).2
  rw [hinv] at h1
  have h2 := mul_mem (T_le h1) t_mem
  rwa [inv_mul_cancel_right] at h2

end CertificateChecks.Batch7092

namespace Certificates

open CertificateChecks

theorem certificate7092 : CFSG.Quasithin.RuRank3.inTitsA CFSG.Quasithin.titsPiArr = true := by
  have hrep : Rep 1755 CFSG.Quasithin.titsPiArr (permOfArr 1755 (unpack 1755 11 TitsPi.P)) := by
    rw [CertificateChecks.Batch7092.pi_eq]
    exact (rep_of TitsPi.perm).1
  have hm := CertificateChecks.Batch7092.mem
  rw [← titsQA_original] at hm
  exact (siftA_iff_mem_ofArrays (n := 1755) (hn := by norm_num) (hk := by
      rw [titsAmbientArrs_size]; norm_num) (hb := by decide) (chunks := 4)
    titsChains_check.2.2.2.2.2.1 (by norm_num) titsChains_check.2.2.2.2.2.2.2.2.1 hrep).2 hm

end Certificates

end
