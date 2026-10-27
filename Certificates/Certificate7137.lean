module

import CFSG.Certificates.Kernel.PermCent.U33Sound
import Certificates.Kernel.PermCent.KU33
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier in
theorem certificate7137 : (pa * pb) ^ 7 = 1 ∧ pa * pb ≠ 1 ∧
    ((elemsT QP).filter fun g =>
      (List.range 7).any fun i => decide (g * (pa * pb) * g⁻¹ = (pa * pb) ^ i)).length = 21 := by
  obtain ⟨h1, h2, h3⟩ := U33T.k7137
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_ev_cOf pa, eq_ev_cOf pb, ev_mul', ev_pow', one_eq_ev, ev_eq_iff]
    exact h1
  · rw [eq_ev_cOf pa, eq_ev_cOf pb, ev_mul', ne_eq, one_eq_ev, ev_eq_iff]
    exact h2
  · rw [U33T.sylow7_eq]
    exact h3

end Certificates
