module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F4
public import CFSG.Quasithin.Vol2.Ch12Sec4N6QW
public import CFSG.Quasithin.Vol2.Ch12Sec4N6E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem normalizerR1Le1246_ofW (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12210 : Stmt12_2_10) (hMS : C134L32CorrM)
    (hSL : BlockQ1246SL27) : NormalizerR1Le1246 := by
  intro G _ _ T L V hcx h3 E hEV hE4 hTE
  obtain ⟨z, v, _, c⟩ := N1246.exists_ctx h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 hcx h3 hEV
    hE4 hTE
  by_contra hN
  have hQ := c.Q_eqW hSL hMS hN
  by_cases hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)
  · exact c.false_of_le_N_L1 hQ hN hL1
  · obtain ⟨g, hg⟩ := c.exists_cyc hN
    exact hg.false_of_not_le_N_L1 h12210 (c.commutator_Q_eqW hMS hN) hL1

theorem lemma12_4_6_of_inputsW (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12210 : Stmt12_2_10) (hMS : C134L32CorrM)
    (hSL : BlockQ1246SL27) : Lemma12_4_6 :=
  lemma12_4_6_of h331 h1222 hpre
    (normalizerR1Le1246_ofW h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 h12210 hMS hSL)

end CFSG.Quasithin.H13
