module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Vanishing.CentralizedLocalSylows
import CFSG.RankThree.PartOne.S9.Alpha.VerificationReduction

public section

namespace CFSG.RankThree.PartOne

theorem alphaZeroOddIntersection_of (hPSR : ProperSubgroupResidual)
    (hAZSC : AlphaZeroSylowCentralization) : AlphaZeroOddIntersection := by
  intro G _ _ p hsec hgood A hA hAcard B hBA hBcard hα
  have : IsSimpleGroup G := hsec.simple
  have hp2 : p ≠ 2 := by have := hsec.three_lt; omega
  refine centralizedLocalSylowsOddIntersections G hsec.nonabelian hsec.charTwo p hsec.prime hp2
    A hA hAcard ?_ (hAZSC G p hsec hgood A hA hAcard B hBA hBcard hα).2 B hBA hBcard
  intro D hDA hDcard K hDK hKtop t htD ht1
  exact hPSR G hsec.kProper (by rw [hsec.evenRank_eq]) p hsec.prime hsec.three_lt D
    (AlphaTheory.isElementaryAbelian_of_le_alpha hA hDA) hDcard K hDK hKtop t htD ht1

end CFSG.RankThree.PartOne
