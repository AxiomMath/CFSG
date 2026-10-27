module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.LocalAnalysis.UniquenessCase.UCK47One
import CFSG.LocalAnalysis.UniquenessCase.UCK47Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem k47 : K47 := by
  intro G _ _ _ V _ _ _ ρ hρ q r hq hr hq2 hr2 hqr D hD hfix
  exact ⟨fun R hR hDR c hc hcz => k47_one ρ hρ hr hr2 D hD hfix R hR hDR c hc hcz,
    fun Q hQ hQab hDQ hQD => k47_two ρ hρ hq hr hq2 hr2 hqr D hD hfix Q hQ hQab hDQ hQD⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
