module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105AutOddU4Red
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105AutOddU5Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kU45AutOdd_holds : KU45AutOdd := by
  intro X _ _ n hX S _ _ B₀ hB α hα hK hS
  have hB' : F08.NotationB8103 ⊤ ⊤ n B₀ := ⟨hB.1, le_top, hB.2.2⟩
  have hB₀ : ∀ x ∈ B₀, α x = x := fun x hx => hS x (hB.2.1 hx)
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · exact AutOdd.eq_one_of_isU5_of_fix hU5 hB' α hα hK hB₀
  · exact AutOdd.eq_one_of_isU4_of_fix hU4 hn hB' α hα hK hB₀

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
