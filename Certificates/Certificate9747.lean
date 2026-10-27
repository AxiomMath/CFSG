module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import CFSG.Certificates.Kernel.ONanSmall.EdgeKSound
import CFSG.Certificates.Kernel.ONanSmall.KTreeSound
import Certificates.Kernel.ONanSmall.M12
public import Certificates.Data.Kernel.PermCent.CV

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  Certificates.Kernel.ONanSmall

theorem certificate9747 : CFSG.ClassicalInvolution.Q3.TA3.Check.verdictCheck 100 [(1 : Equiv.Perm (Fin 24))]
    (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D) true
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D)) = true := by
  have hm : ∀ L : List (CV 24), L.map ev = L.map (evHom 24) := fun _ => rfl
  have h1 : [(1 : Equiv.Perm (Fin 24))] = [(1 : CV 24)].map (evHom 24) := by
    rw [List.map_singleton, map_one]
  rw [h1, elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, verdictCheck_map _ ev_injective,
    verdictCheck_pickReps _ _ _ _ M12.one_mem,
    pickReps_of_pickRun _ invC conjC (genC m12D) invC_eq conjC_eq (genC_mem m12D) _ _ M12.pick]
  have hC : M12.reps.map (centB (elemsC m12D)) = M12.cents := by
    exact (map_centB_eq _ _).trans M12.cent_ok
  refine all_cent_of (fun t C => noOddB3 100 C && pairsV 100 [1] (elemsC m12D) true t C) hC ?_
  rw [List.all_eq_true]
  intro p hp
  have h := List.all_eq_true.1 M12.k9747 p hp
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i he
    rw [pairsVKF_eq] at h2
    refine pairsV_of_pairsVK (K := CFSG.KD.ONS.M12.K0.map M12.el) (fun g hg => ?_) h2
    have hcl : ∀ T ∈ TsC m12D, ∀ u ∈ T, ∀ k ∈ CFSG.KD.ONS.M12.K0.map M12.el,
        u⁻¹ * k * u ∈ CFSG.KD.ONS.M12.K0.map M12.el := fun T hT u hu k hk =>
      KTree.mem_of_memK_ofList _ (List.all_eq_true.1
        (List.all_eq_true.1 (List.all_eq_true.1 M12.cls0 T hT) u hu) k hk)
    have ht0 : M12.reps.getD 0 1 ∈ CFSG.KD.ONS.M12.K0.map M12.el := by
      have hc := M12.t0_mem
      unfold memB at hc
      obtain ⟨s, hs, e⟩ := List.any_eq_true.1 hc
      rw [decide_eq_true_eq] at e
      rw [← e]
      exact hs
    rw [he]
    rw [elemsC_eq] at hg
    exact conj_mem_productsOf _ hcl g hg _ ht0
  · exact h2

end Certificates
