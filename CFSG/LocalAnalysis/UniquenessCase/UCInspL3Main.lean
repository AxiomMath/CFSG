module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3L
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

theorem inspL3_holds : InspL3 := by
  intro G _ _ hG D hD
  rcases hG with ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩
  · obtain ⟨ℓ, R, hℓ, hℓ2, hℓ3, hpair⟩ := inspL3_L hq hL D hD
    exact ⟨ℓ, R, hℓ, hℓ2, hℓ3, hpair⟩
  · obtain ⟨ℓ, R, hℓ, hℓ2, hℓ3, hpair⟩ := inspL3_U hq hL D hD
    exact ⟨ℓ, R, hℓ, hℓ2, hℓ3, hpair⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
