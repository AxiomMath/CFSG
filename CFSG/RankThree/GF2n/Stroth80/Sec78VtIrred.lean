module

public import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmegaTwo
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec78CentreStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7VtIrred_holds : Sec7VtIrredStatement := by
  intro G _ _ M Q Z B hc n t hs U hZU hUV hRU
  obtain ⟨m, hm, h | h⟩ := hs.orth
  · obtain ⟨K, fK, finK, hK, hrep⟩ := h
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs.notPlus4 ⟨K, fK, finK, hK, hrep⟩
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    exact hrep.eq_or_eq_of_invariant (natIrred_statedOmegaPlus hm3)
      (addCommutantScalar_statedOmegaPlus hm3) hZU hUV hRU
  · obtain ⟨K, fK, finK, hK, b, c, hirr, hrep⟩ := h
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hirrG : NatIrred (StatedOmega (StatedQuadMinus m K b c)) := by
      rcases Nat.eq_or_lt_of_le hm with h2 | h3
      · subst h2
        exact natIrred_statedOmegaMinus_two hirr
      · exact natIrred_statedOmegaMinus_of_three_le h3 hirr
    exact hrep.eq_or_eq_of_invariant hirrG (addCommutantScalar_statedOmegaMinus hm hirr)
      hZU hUV hRU

end CFSG.RankThree.GF2n.Stroth80
