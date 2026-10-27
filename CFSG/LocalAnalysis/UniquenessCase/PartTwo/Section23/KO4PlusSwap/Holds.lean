module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Transport
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFourComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NaturalO4PlusSubnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kO4PlusSwap_holds : KO4PlusSwap := by
  intro W _ _ R L S e hnat hL hLs hS hSN
  obtain ⟨K₀, _, _, hK₀, h4, -⟩ :=
    PartTwo.exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hL hLs hnat
  obtain ⟨K, _, _, _, hK, ⟨φ⟩⟩ := KO4Swap.exists_mulEquiv_determinantIsometries hnat
  have hK4 : 4 ≤ Nat.card K := by rw [hK, ← hK₀]; exact h4
  have hLR : L ≤ R := CFSG.Open.IsSubnormal.le hLs
  exact ComponentInitial.not_le_normalizer_of_isSubnormal hK4
    (KO4Swap.isQuasisimple_map φ hL hLR) (KO4Swap.isSubnormal_map φ hLs)
    (KO4Swap.not_two_dvd_index_map φ hS) (KO4Swap.map_le_normalizer_map φ hS.1 hLR hSN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
