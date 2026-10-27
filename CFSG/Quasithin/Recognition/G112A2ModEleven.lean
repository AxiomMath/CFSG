module

public import CFSG.Quasithin.Recognition.G112A2ModStmts
public import CFSG.Quasithin.Recognition.G112A2ModElevenInvol

public section

namespace CFSG.Quasithin.G112A2

theorem g112A2OpenConcl11_holds : G112A2OpenConcl11 := by
  intro V _ _ _ B Γ v₁ W X X₀ hH hC t ht hr _ _
  obtain ⟨_, hL⟩ := hC
  have htΓ : t ∈ Γ := hH.X_le ht
  have ht2 : t * t = 1 := hH.X_sq t ht
  have htL : t ∈ CFSG.ASVolI.ChG.fStarIn Γ := Eleven.involution_mem_fStarIn hL htΓ ht2
  exact absurd hr (Eleven.finrank_range_ne_two_of_mem hL htL ht2)

end CFSG.Quasithin.G112A2

end
