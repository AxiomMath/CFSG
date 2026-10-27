module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFour
import CFSG.LocalAnalysis.WeakClosure81.SixEighteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w3_6_18_holds (G : Type) [Group G] [Finite G] : S17.W3_6_18 G := by
  intro V M H S H₁ H₂ hV _ _ _ hS _ k _ hH hS₁ _ _ hF₁ hS₂ _ _ hF₂ hU hgt hW0
  exact CFSG.LocalAnalysis.WeakClosure81.six_eighteen hV hS hH hS₁ hF₁ hS₂ hF₂ hU hW0 hgt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
