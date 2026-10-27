module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Check
public import CFSG.GH74.KGroups.U33Inputs
import CFSG.Certificates.Kernel.ONanSmall.Q16Sound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.Q16U33

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.CGT.PushingUpLit.SolKNA.R4.Check
  CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate9754 : CFSG.CGT.PushingUpLit.SolKNA.R4.Check.noQ16Check
    (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA)
    (CFSG.ClassicalInvolution.Q3.TA3.Check.pickReps
      (CFSG.GH74.KGroups.elemsT CFSG.GH74.KGroups.U33.QA)) = true := by
  have hm : ∀ L : List (CV 28), L.map ev = L.map (evHom 28) := fun _ => rfl
  rw [elemsT_eq_elemsC, hm, pickReps_map _ ev_injective, noQ16Check_map _ ev_injective,
    noQ16Check_pickReps U33A.one_mem,
    pickReps_of_pickRun _ invC conjC (genC CFSG.GH74.KGroups.U33.QA) invC_eq conjC_eq
      (genC_mem CFSG.GH74.KGroups.U33.QA) _ _ U33A.pick]
  have hC : U33A.reps.map (centB (elemsC CFSG.GH74.KGroups.U33.QA)) = U33A.cents :=
    (map_centB_eq _ _).trans U33A.cent_ok
  exact all_cent_of (fun t C => q16At t C) hC Q16.k9754

end Certificates
