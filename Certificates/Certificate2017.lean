module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA7Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A7
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.FootePkSound
import Certificates.Kernel.SchreierFam.C2017K

public section

namespace Certificates

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A7
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A7 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.FooteSmall in
open CFSG.ComponentClassification.FooteSmall.A7 CFSG.GH74.KGroups CFSG.GH74.KGroups.A7 in
theorem certificate2017 : (closedCheck Q0list = true)
    ∧ (Q0list.Nodup)
    ∧ (Q0list.length = 2 ^ 4)
    ∧ (Q0list.all (fun g => QA.sift g 0) = true)
    ∧ ((a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
      dihB a0 b0 = true
    )
    ∧ (pairCheck 5 2 Q0list (elemsT QP) [pa, pb] = true) := by
  simp only [sift_eq_siftP]
  rw [elemsT_eq_elemsV, elemsV]
  exact ⟨closed_2017K, nodup_2017K, length_2017K, sift_2017K, ab_2017K,
    pairCheck_of (by norm_num) 2 _ _ _ pair_2017K⟩

end Certificates
