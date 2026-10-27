module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431


theorem f431Generation_g2 (f : ℕ) : F431Generation .G2 0 f := by
  intro D _ hD A
  obtain ⟨-, K, hF, hFin, hcp, h3, -, ⟨e⟩⟩ := g2_quot_data hD
  have := isSimpleGroup_adjointQuotient h3
  exact BN.range_conj_le_of_rankTwo (g2ModelSystem K h3) (isSylowTwoOf_modelU h3) e A

theorem f431Facts45_g2 (f : ℕ) (hm : F431ModelFacts .G2 0 f) : F431Facts45 .G2 0 f hm := by
  intro D _ hD A
  obtain ⟨-, K, hF, hFin, hcp, h3, -, ⟨e⟩⟩ := g2_quot_data hD
  have := isSimpleGroup_adjointQuotient h3
  exact BN.facts45L_of_rankTwo (g2ModelSystem K h3) (isSylowTwoOf_modelU h3) (hm D hD).1
    (by norm_num) e A

end CFSG.Quasithin.H13.F431.G2
