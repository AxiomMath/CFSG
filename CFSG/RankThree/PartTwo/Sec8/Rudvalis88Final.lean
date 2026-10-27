module

public import CFSG.RankThree.PartTwo.Sec8.Rudvalis88Partner
public import CFSG.RankThree.PartTwo.Sec8.Rudvalis88Swap
public import CFSG.RankThree.PartTwo.Sec8.Hering88LCFinal
public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm2P1

public section

namespace CFSG.RankThree.PartTwo.Sec8.Rudvalis88

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item86ResProof

theorem partnerGamma88_of (h83 : Item83) (h45 : Sec4.Item4_5) (h418 : Item418Theta)
    (hL82 : Item82TwoList) : Hering88N.PartnerGamma88 := by
  intro G _ _ A c L a b X n h Y _ hIJ x A₀ d' m hodd hc1
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  rcases hcases with ⟨hRee, -⟩ | ⟨-, hK⟩
  · exact (false_of_ree_of_case1 h hRee (le_sup_left.trans hIJ) hodd hc1).elim
  · exact partner_isGammaIndex_of_projSL h83 h45 h418 hL82 h hK

theorem item88_of_partner (h48 : Sec4.Item4_8) (h418 : Item418Theta) (h45 : Sec4.Item4_5)
    (h83 : Item83) (hF : KF84Field) (hL82 : Item82TwoList) : Item88 := by
  have h84 : Pair84A := pair84A_of h418 hF
  have hPG := partnerGamma88_of h83 h45 h418 hL82
  have h47 := Hering88C.inputs47ClassesD4_holds
  have hG2 := Hering88F.g2TwoCentThreeSolvable_holds
  exact item88_of_step h48 h418 hF
    (Hering88E.kF88Step_of_case1ClassB h45 h84 h83 hF
      (Hering88F.kF88Case1ClassB_of_three h45 hF hG2
        (Hering88N.kF88Case1ClassBSwap_of_partner h45 hF h84 hPG hG2
          (Hering88N.kF88Case1ClassBSwapRest_of h45 h47 h84 hPG))
        (Hering88N.kF88Case1ClassBOne_of h45 h47 h83 h84 hPG)
        (Hering88N.kF88Case1ClassBPGU_of h45 h83 h84 hF hPG))
      (Hering88LC.kF88LinkCoreD83_of h45 h83 h418 hF))

end CFSG.RankThree.PartTwo.Sec8.Rudvalis88

end
