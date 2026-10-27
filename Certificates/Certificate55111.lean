module

public import Certificates.Data.TL4MF163U3Inv
import CFSG.Certificates.Kernel.ONanSmall.MapSound
import CFSG.Certificates.Kernel.ONanSmall.CVGlue
import Certificates.Kernel.ONanSmall.U33A

public section

namespace Certificates

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.ONanSmall CFSG.KC.ONanSmall
  CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups Certificates.Kernel.ONanSmall

theorem certificate55111 : Certificates.TL4MF163U3Inv.u33CentInvCk () = true := by
  have hm : ∀ L : List (CV 28), L.map ev = L.map (evHom 28) := fun _ => rfl
  unfold Certificates.TL4MF163U3Inv.u33CentInvCk
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC, hm, hm, pickReps_map _ ev_injective,
    centInvCheck_map _ ev_injective,
    pickReps_of_pickRun _ invC conjC (genC U33.QA) invC_eq conjC_eq (genC_mem U33.QA) _ _
      U33A.pick]
  have hC : U33A.reps.map (centB (elemsC U33.QA)) = U33A.cents := by
    exact (map_centB_eq _ _).trans U33A.cent_ok
  exact all_cent_of (fun t C => Certificates.TL4MF163U3Inv.centInvAt (elemsC U33.QP) t C) hC
    U33A.k55111

end Certificates
