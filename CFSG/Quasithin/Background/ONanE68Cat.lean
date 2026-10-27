module

public import CFSG.Quasithin.Background.ONanE68Cases
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2pB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem smallCatL33_holds :
    SmallCatL33 :=
  fun X _ _ h => Unc25L33.l33_facts X h

theorem smallCatL2p_holds :
    SmallCatL2p := by
  intro X _ _ p hFM h7 hmodel
  rcases h7.lt_or_eq with h7' | h7'
  · exact Unc25Small.l2p_facts hFM h7' X hmodel
  · subst h7'
    obtain ⟨K, _, _, _, e, hcard, -, -⟩ :=
      CFSG.QuasithinUnique.K1.psl2_model_data (by norm_num) hmodel
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hK : Nat.card K = 7 := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
    have H : Unc25Small.L2pHyp K 7 := ⟨le_rfl, hK, Or.inr ⟨by norm_num, 3, by norm_num⟩⟩
    exact ⟨Unc25Small.SmallListFacts.of_mulEquiv e (Unc25Small.psl2_smallListFacts H),
      Unc25Small.FixPointwiseInner.of_mulEquiv e (Unc25Small.psl2_fixPointwiseInner H)⟩

end E68Proof

end E6

end CFSG.Quasithin
