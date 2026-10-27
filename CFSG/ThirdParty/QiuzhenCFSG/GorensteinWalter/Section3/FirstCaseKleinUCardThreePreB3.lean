module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountEquations14
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIdentityEight
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountConstructor
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The Klein branch already forces `|U| = 3` before the separate `J₃`
elimination: restrictions (5)--(7) give finite support, and the commuting
pair identity (8) then feeds the order-three count lemma. -/
public theorem firstCase_klein_U_card_three_pre_b3
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nat.card c.U = 3 := by
  classical
  have h7 := firstCase_klein_restriction_seven_data hmin c hfirst hklein
  have hvanish : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 :=
    firstCase_klein_high_fiber_vanish_of_n_eq_four hmin c hfirst hklein h7
  obtain ⟨K, b0, b1, b2, b3, b4, hKHall, hKne, hJn, hHcount,
      hHhatcount, _hindex, _htotal, _hsum, h4⟩ :=
    firstCase_klein_count_equations_one_to_four hmin c hfirst hklein hvanish
  have h8 := firstCase_klein_identity_eight hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hHcount hHhatcount hJn h7
  exact firstCase_klein_U_card_three_of_count hmin c hfirst hklein
    K b0 b1 b2 b3 b4 hKHall hKne hJn h8 h4

end CFSG.GorensteinWalter
