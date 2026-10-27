module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CoverSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.P43A

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  Certificates.Kernel.ONanSmall

theorem certificate9746 : CFSG.ClassicalInvolution.Q3.TA3.Check.verdictCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45)
    (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45) false
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45)) = true := by
  have hm : ∀ L : List (CV 45), L.map ev = L.map (evHom 45) := fun _ => rfl
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, hm, hm, pickReps_map _ ev_injective,
    verdictCheck_map _ ev_injective, verdictCheck_pickReps _ _ _ _ P43A.one_mem,
    pickReps_of_pickRun _ invC conjC (genC PSp43.QA45) invC_eq conjC_eq (genC_mem PSp43.QA45) _ _
      P43A.pick]
  have hC : P43A.reps.map (centB (elemsC PSp43.QA45)) = P43A.cents := by
    exact (map_centB_eq _ _).trans P43A.cent_ok
  exact all_cent_of (fun t C => noOddB3 100 C &&
    pairsV 100 (elemsC PSp43.QP45) (elemsC PSp43.QA45) false t C) hC P43A.k9746

end Certificates
