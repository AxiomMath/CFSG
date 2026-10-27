module

public import CFSG.RankThree.GF2n.Smith81.LinOddCore
public import CFSG.RankThree.GF2n.Smith81.LinCoord
public import CFSG.RankThree.GF2n.Smith81.LinGamma

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Lin28aOddBelowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n : ℕ)
    (V₁ V₂ : Subgroup G), Smith1981Below (Nat.card G) → Ctx M Q Z B →
    LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → Odd n → Sit M Q Z X x → Q ⊓ QB X ≠ ⊥

theorem lin28aOdd_of (h31 : Lin31Statement)
    (h212c : Lin212CondStatement) : Lin28aOddBelowStatement := by
  intro G _ _ M Q Z B X x n V₁ V₂ hb hc hS hn3 hodd hs
  obtain ⟨m, hm⟩ := hodd
  have hm1 : 1 ≤ m := by omega
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := h31 G M Q Z B n V₁ V₂ hb hc hS (by omega)
  have hcond := h212c G M Q Z B n V₁' V₂' hb hc hS' hn3
  exact lin28aOdd_core linSwapStatement_holds linNonswapStatement_holds linGammaStatement_holds
    linRankBoundStatement_holds hc hS' hm hm1 (OddSetup.of_linSetup hc hS' h31') hcond hs

end CFSG.RankThree.GF2n.Smith81
