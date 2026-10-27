module

public import Certificates.Data.TL4LieZ2Inv
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.L33
import Certificates.Kernel.ONanSmall.M11

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate55123 : Certificates.TL4LieZ2Inv.l33Q8InvCk () = true ∧
    Certificates.TL4LieZ2Inv.m11Q8InvCk () = true := by
  refine ⟨?_, ?_⟩
  · have hm : ∀ L : List (CV 26), L.map ev = L.map (evHom 26) := fun _ => rfl
    unfold Certificates.TL4LieZ2Inv.l33Q8InvCk
    dsimp only
    rw [elemsT_eq_elemsC, elemsT_eq_elemsC, hm, hm, pickReps_map _ ev_injective,
      q8InvCheck_map _ ev_injective, Certificates.TL4LieZ2Inv.q8InvCheck,
      coverB_pickReps L33.oneP_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genC L33.QP) invC_eq conjC_eq (genC_mem L33.QP) _ _
        L33.pickP]
    have hC : L33.repsP.map (centB (elemsC L33.QP)) = L33.centsP := by
      exact (map_centB_eq _ _).trans L33.centP_ok
    have hD : L33.repsP.map (centB (elemsC L33.QA)) = L33.centsPA := by
      exact (map_centB_eq _ _).trans L33.centPA_ok
    exact all_cent2_of (fun t C D => Certificates.TL4LieZ2Inv.q8InvAt t C D) hC hD L33.k55123
  · have hm : ∀ L : List (CV 11), L.map ev = L.map (evHom 11) := fun _ => rfl
    unfold Certificates.TL4LieZ2Inv.m11Q8InvCk
    dsimp only
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, q8InvCheck_map _ ev_injective,
      Certificates.TL4LieZ2Inv.q8InvCheck, coverB_pickReps M11.one_mem, Bool.true_and,
      pickReps_of_pickRun _ invC conjC (genC M11.Q) invC_eq conjC_eq (genC_mem M11.Q) _ _ M11.pick]
    have hC : M11.reps.map (centB (elemsC M11.Q)) = M11.cents := by
      exact (map_centB_eq _ _).trans M11.cent_ok
    exact all_cent_of (fun t C => Certificates.TL4LieZ2Inv.q8InvAt t C C) hC M11.k55123

end Certificates
