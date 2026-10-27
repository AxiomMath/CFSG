module

public import Certificates.Data.GH74.PSp43NoQ8
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.P43P
import Certificates.Kernel.ONanSmall.P43A

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  Certificates.Kernel.ONanSmall

theorem certificate55108 : Certificates.PSp43NoQ8.chkP () = true ∧ Certificates.PSp43NoQ8.chkA () = true := by
  have hm : ∀ L : List (CV 45), L.map ev = L.map (evHom 45) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · unfold Certificates.PSp43NoQ8.chkP
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ8Check_map _ ev_injective,
      pickReps_of_pickRun _ invC conjC (genC PSp43.QP45) invC_eq conjC_eq (genC_mem PSp43.QP45) _ _
        P43P.pick]
    have hC : P43P.reps.map (centB (elemsC PSp43.QP45)) = P43P.cents := by
      exact (map_centB_eq _ _).trans P43P.cent_ok
    exact all_cent_of (fun t C => Certificates.PSp43NoQ8.noQ8PairsB t C) hC P43P.k55108
  · unfold Certificates.PSp43NoQ8.chkA
    rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ8Check_map _ ev_injective,
      pickReps_of_pickRun _ invC conjC (genC PSp43.QA45) invC_eq conjC_eq (genC_mem PSp43.QA45) _ _
        P43A.pick]
    have hC : P43A.reps.map (centB (elemsC PSp43.QA45)) = P43A.cents := by
      exact (map_centB_eq _ _).trans P43A.cent_ok
    exact all_cent_of (fun t C => Certificates.PSp43NoQ8.noQ8PairsB t C) hC P43A.k55108

end Certificates
