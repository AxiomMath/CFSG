module

public import CFSG.Sporadic.Co2Smith.GlWMark
public import CFSG.Sporadic.Co2Smith.GlC0Fusion

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert

theorem smithC0Input_of_NJChart
    (h : SmithNJChart) : SmithC0Input C0c α3c := by
  intro G _ _ z hs hG φ hglob
  obtain ⟨ψ, hψ⟩ := h G z hs hG φ hglob
  have hz : phiH φ z0C = z := by
    rw [phiH_apply, ← φ_zH hG.orderOf_eq φ, MulEquiv.symm_apply_apply]
    rfl
  exact exists_smithC0Marking_of_chart hψ hz

end CFSG.Sporadic.Co2Smith
