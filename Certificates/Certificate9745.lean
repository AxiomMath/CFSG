module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CoverSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.P43P

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall
  Certificates.Kernel.ONanSmall

theorem certificate9745 : CFSG.ClassicalInvolution.Q3.TA3.Check.verdictCheck 100 [(1 : Equiv.Perm (Fin 45))]
    (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45) false
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45)) = true := by
  have hm : ∀ L : List (CV 45), L.map ev = L.map (evHom 45) := fun _ => rfl
  have h1 : [(1 : Equiv.Perm (Fin 45))] = [(1 : CV 45)].map (evHom 45) := by
    rw [List.map_singleton, map_one]
  rw [h1, elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, verdictCheck_map _ ev_injective,
    verdictCheck_pickReps _ _ _ _ P43P.one_mem,
    pickReps_of_pickRun _ invC conjC (genC PSp43.QP45) invC_eq conjC_eq (genC_mem PSp43.QP45) _ _
      P43P.pick]
  have hC : P43P.reps.map (centB (elemsC PSp43.QP45)) = P43P.cents := by
    exact (map_centB_eq _ _).trans P43P.cent_ok
  exact all_cent_of (fun t C => noOddB3 100 C && pairsV 100 [1] (elemsC PSp43.QP45) false t C) hC
    P43P.k9745

end Certificates
