module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A6
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.FootePkSound
import Certificates.Kernel.SchreierFam.C2016K

public section

namespace Certificates

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A6
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.FooteSmall in
open CFSG.ComponentClassification.FooteSmall.A6 CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 in
theorem certificate2016 : (closedCheck Q0list = true)
    ∧ (Q0list.Nodup)
    ∧ (Q0list.length = 2 ^ 5)
    ∧ (Q0list.all (fun g => QA.sift g 0) = true)
    ∧ ((a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
      dihB a0 b0 = true
    )
    ∧ (pairCheck 3 4 Q0list (elemsT QP) [pa, pb] = true) := by
  simp only [sift_eq_siftP]
  rw [elemsT_eq_elemsV, elemsV]
  exact ⟨closed_2016K, nodup_2016K, length_2016K, sift_2016K, ab_2016K,
    pairCheck_of (by norm_num) 4 _ _ _ pair_2016K⟩

end Certificates
