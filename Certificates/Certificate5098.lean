module

public import CFSG.GH74.GLS.Prop27.OddCoreCheck
import CFSG.Certificates.Kernel.PermCent.KGrpC2Sound
import CFSG.Certificates.Kernel.PermCent.KGrpOddConjSound
import Certificates.Kernel.Misc.KGroups.U33Valid
import Certificates.Kernel.PermCent.K5098C
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.Certificates CFSG.Sporadic.Schreier

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Prop27 in
open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier in
theorem certificate5098 : oddCoreCheck 189 (elemsT U33.QA) (elemsT U33.QP) = true := by
  have hQP : ValidSchreier QP := KernelMisc.U33PC.valid
  have hQA : ValidSchreier QA := KernelMisc.U33AC.valid
  have hle : QP.originalSubgroup ≤ QA.originalSubgroup := by
    rw [QP, QA, certificate_originalSubgroup, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    apply Subgroup.subset_closure
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
    rcases hg with rfl | rfl <;> simp
  have hmem : ∀ (Q : RawSchreierDatum 28) (hQ : ValidSchreier Q) (c : CV 28),
      siftC Q c 0 = true → c ∈ elemsC Q := fun Q hQ c h =>
    (mem_elemsC Q hQ c).2 ((mem_iff_sift Q hQ _).2 (by rw [sift_ev]; exact h))
  have hbP : cOf pt2 ∉ elemsC QP := fun h => by
    have h1 := (mem_iff_sift QP hQP _).1 ((mem_elemsC QP hQP _).1 h)
    rw [sift_ev, K5098C.kRep.2.2.2.1] at h1
    exact Bool.false_ne_true h1
  have hcl := conj_of_count QA QP hQA hQP hle (cOf pu) (cOf pt2) 63 252
    (by rw [K5098C.kP, K5098C.kU.1]) (by rw [K5098C.kP, K5098C.kT.1]) K5098C.kInv
    (hmem QA hQA _ K5098C.kRep.1) (hmem QA hQA _ K5098C.kRep.2.1) K5098C.kRep.2.2.2.2.1
    K5098C.kRep.2.2.2.2.2 (hmem QP hQP _ K5098C.kRep.2.2.1) hbP
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, oddCoreCheck_C]
  refine oddCoreCheckC_of_reps QA QP hQA hQP hle 189 [cOf pu, cOf pt2] hcl fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact K5098C.kU.2
  · exact K5098C.kT.2

end Certificates
