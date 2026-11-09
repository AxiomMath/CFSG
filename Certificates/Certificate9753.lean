module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.ONanSmall.Q16Sound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.Q16L33

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check
  CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate9753 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.L33.QA)) = true := by
  have hm : ∀ L : List (CV 26), L.map ev = L.map (evHom 26) := fun _ => rfl
  rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ16Check_map _ ev_injective,
    noQ16Check_pickReps L33.oneA_mem,
    pickReps_of_pickRun _ invC conjC (genC CFSG.GH74.KGroups.L33.QA) invC_eq conjC_eq
      (genC_mem CFSG.GH74.KGroups.L33.QA) _ _ L33.pickA]
  have hC : L33.repsA.map (centB (elemsC CFSG.GH74.KGroups.L33.QA)) = L33.centsA :=
    (map_centB_eq _ _).trans L33.centA_ok
  exact all_cent_of (fun t C => q16At t C) hC Q16.k9753

end Certificates
