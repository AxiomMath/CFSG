module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.GH74.KGroups.U33Inputs
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import CFSG.Certificates.Kernel.ONanSmall.EdgeKSound
import Certificates.Kernel.ONanSmall.U33A
public import Certificates.Data.Kernel.PermCent.CV

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate9744 : CFSG.ClassicalInvolution.Q3.TA3.Check.verdictCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QP)
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA) false
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA)) = true := by
  have hm : ∀ L : List (CV 28), L.map ev = L.map (evHom 28) := fun _ => rfl
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, hm, hm, pickReps_map _ ev_injective,
    verdictCheck_map _ ev_injective, verdictCheck_pickReps _ _ _ _ U33A.one_mem,
    pickReps_of_pickRun _ invC conjC (genC U33.QA) invC_eq conjC_eq (genC_mem U33.QA) _ _
      U33A.pick]
  have hC : U33A.reps.map (centB (elemsC U33.QA)) = U33A.cents := by
    exact (map_centB_eq _ _).trans U33A.cent_ok
  refine all_cent_of (fun t C => noOddB3 100 C && pairsV 100 (elemsC U33.QP) (elemsC U33.QA)
    false t C) hC ?_
  rw [List.all_eq_true]
  intro p hp
  have h := List.all_eq_true.1 U33A.k9744 p hp
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i he
    refine pairsV_of_pairsVK (K := CFSG.KD.ONS.U33A.K1.map U33A.el) (fun g hg => ?_) h2
    have hc := List.all_eq_true.1 U33A.cls1 g hg
    rw [he]
    unfold memB at hc
    obtain ⟨s, hs, e⟩ := List.any_eq_true.1 hc
    rw [decide_eq_true_eq] at e
    rw [← e]
    exact hs
  · exact h2

end Certificates
