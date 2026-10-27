module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.ONanSmall.Q16Sound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.Q16M12

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Certificates.Kernel.ONanSmall

theorem certificate9756 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
        (fun d => CFSG.Sporadic.Schreier.m12Sigma * d))
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D ++
      (CFSG.GH74.KGroups.elemsT CFSG.Sporadic.Schreier.m12D).map
        (fun d => CFSG.Sporadic.Schreier.m12Sigma * d))) = true := by
  rw [elemsT_append_map m12D m12Sigma, pickReps_map (evHom 24) ev_injective,
    noQ16Check_map (evHom 24) ev_injective, noQ16Check_pickReps M12A.one_mem,
    pickReps_of_pickRun _ invC conjC (genA m12D M12A.sig) invC_eq conjC_eq
      (genA_mem m12D M12A.sig) _ _ M12A.pick]
  have hC : M12A.reps.map (centB M12A.LA) = M12A.cents := (map_centB_eq _ _).trans M12A.cent_ok
  exact all_cent_of (fun t C => q16At t C) hC Q16.k9756

end Certificates
