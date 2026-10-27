module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K21165

public section

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
  CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups in
theorem certificate21165 :
    ((elemsT QP45).filter (fun g => decide (g * x45 = x45 * g))).length = 576 := by
  have hf : ((fun g => decide (g * x45 = x45 * g)) ∘ ev) =
      fun g : CV 45 => eq22C g (cOf x45) (cOf x45) g := by
    funext g
    rw [Function.comp_apply, decide_comm_ev, comm_fast]
  have h := Nat.eq_of_beq_eq_true K21165.k21165
  unfold K21165.cnt21165 at h
  rw [elemsT_eq_elemsC, List.filter_map, hf, List.length_map]
  exact h

end Certificates
