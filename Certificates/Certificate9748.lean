module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.M12A

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  Certificates.Kernel.ONanSmall

theorem certificate9748 : CFSG.ClassicalInvolution.Q3.TA3.Check.verdictCheck 100
    (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D)
    (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
        (fun d => CFSG.Sporadic.Schreier.m12Sigma * d)) false
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
        (fun d => CFSG.Sporadic.Schreier.m12Sigma * d))) = true := by
  have hm : ∀ L : List (CV 24), L.map ev = L.map (evHom 24) := fun _ => rfl
  rw [elemsT_append_map m12D m12Sigma, elemsT_eq_elemsC m12D, hm,
    pickReps_map (evHom 24) ev_injective, verdictCheck_map (evHom 24) ev_injective,
    verdictCheck_pickReps _ _ _ _ M12A.one_mem,
    pickReps_of_pickRun _ invC conjC (genA m12D M12A.sig) invC_eq conjC_eq
      (genA_mem m12D M12A.sig) _ _ M12A.pick]
  have hC : M12A.reps.map (centB M12A.LA) = M12A.cents := by
    exact (map_centB_eq _ _).trans M12A.cent_ok
  exact all_cent_of (fun t C => noOddB3 100 C && pairsV 100 (elemsC m12D) M12A.LA false t C) hC
    M12A.k9748

end Certificates
