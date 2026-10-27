module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Six
public import CFSG.Quasithin.Background.GoldschmidtTDE68Seven

public section

namespace CFSG.Quasithin.E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

theorem e68CentCompAlt : E68CentCompAlt := by
  intro Y _ _ L R K z u hcases h hK
  rcases hcases with hC | hD
  · exact (Alt.false_comp_caseC hC h hK).elim
  · exact ⟨hD, Alt.card_comp_caseD hD h hK⟩

theorem e68AltRank : E68AltRank := by
  intro Y _ _ L A R z hcases h
  rcases hcases with hC | hD
  · exact Alt.altRank_caseC hC h
  · exact Alt.altRank_caseD hD h

end CFSG.Quasithin.E6
