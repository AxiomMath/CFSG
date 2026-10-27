module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.GH74.KGroups.M11Inputs
import CFSG.Certificates.Kernel.ONanSmall.Q16Sound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.Q16M11

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check
  CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate9752 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.M11.Q)
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.M11.Q)) = true := by
  have hm : ∀ L : List (CV 11), L.map ev = L.map (evHom 11) := fun _ => rfl
  rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ16Check_map _ ev_injective,
    noQ16Check_pickReps M11.one_mem,
    pickReps_of_pickRun _ invC conjC (genC CFSG.GH74.KGroups.M11.Q) invC_eq conjC_eq
      (genC_mem CFSG.GH74.KGroups.M11.Q) _ _ M11.pick]
  have hC : M11.reps.map (centB (elemsC CFSG.GH74.KGroups.M11.Q)) = M11.cents :=
    (map_centB_eq _ _).trans M11.cent_ok
  exact all_cent_of (fun t C => q16At t C) hC Q16.k9752

end Certificates
