module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore

public section

namespace CFSG.StandardType


theorem ggSecFiveBSpCoordFrameInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBSpCoordFrameInput := by
  intro G _ _ p hp hp2 r f hr hf hdvd B Bs X hBs hmark hX eta i0 hA
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ω, hωo⟩ : ∃ ω : (GaloisField 2 f)ˣ, orderOf ω = p :=
    exists_prime_orderOf_dvd_card' p (by
      rw [Nat.card_units, GaloisField.card 2 f (by omega)]
      exact hdvd)
  have hω : ω ^ p = 1 := by
    rw [← hωo]
    exact pow_orderOf_eq_one ω
  obtain ⟨π, hπ0, κ, χ, hF⟩ :=
    ggSecFiveBPermSpK_exists_frame hMp hp2 (by omega) hr hBs hmark (Classical.choice hX) eta hA hω
      hωo
  exact ⟨π, κ, χ, hπ0, hF⟩

end CFSG.StandardType

end
