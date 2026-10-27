module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.Q16Sound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.Q16P43

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check
  CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall Certificates.Kernel.ONanSmall

theorem certificate9755 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45)
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45)) = true := by
  have hm : ∀ L : List (CV 45), L.map ev = L.map (evHom 45) := fun _ => rfl
  rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ16Check_map _ ev_injective,
    noQ16Check_pickReps P43A.one_mem,
    pickReps_of_pickRun _ invC conjC (genC PSp43.QA45) invC_eq conjC_eq (genC_mem PSp43.QA45) _ _
      P43A.pick]
  have hC : P43A.reps.map (centB (elemsC PSp43.QA45)) = P43A.cents :=
    (map_centB_eq _ _).trans P43A.cent_ok
  exact all_cent_of (fun t C => q16At t C) hC Q16.k9755

end Certificates
