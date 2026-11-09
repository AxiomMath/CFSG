module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Check
import CFSG.Certificates.Kernel.PermCent.SmallF3TwinSound
import Certificates.Kernel.PermCent.K8040
import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.L33Inputs

public section

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.SmallF3T

namespace Certificates

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL33 CFSG.GH74.KGroups in
theorem certificate8040 : fourGenCheck (elemsT L33.QA) (elemsT L33.QP) = true := by
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, fourGenCheck_C]
  have hle : L33.QP.originalSubgroup ≤ L33.QA.originalSubgroup := by
    rw [L33.QP_closure, L33.QA, Sporadic.Schreier.certificate_originalSubgroup, Subgroup.closure_le]
    intro x hx
    apply Subgroup.subset_closure
    rcases hx with rfl | hx
    · simp
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]
  exact K8040.k8040 L33.QP_ok L33.QA_ok fun g hg =>
    (KGrp.mem_elemsC L33.QA L33.QA_ok g).2 (hle ((KGrp.mem_elemsC L33.QP L33.QP_ok g).1 hg))

end Certificates
