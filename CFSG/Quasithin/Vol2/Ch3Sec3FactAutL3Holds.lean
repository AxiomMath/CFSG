module

public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Wr
public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3SD
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312

public section

namespace CFSG.Quasithin.H13

open L3Eps

theorem factAutL3Eps_holds : FactAutL3Eps := by
  intro W _ _ hs h
  obtain ⟨p, hp, hp2, hW⟩ := isL3EpsModel_of_hyp hs h
  refine autOddNormCent_of_isL3EpsModel ⟨hp, hp2, hW⟩ ?_
  have hodd : p % 4 = 1 ∨ p % 4 = 3 := by
    have := hp.odd_of_ne_two hp2
    rw [Nat.odd_iff] at this
    omega
  rcases hW with hW | hW
  · rcases hodd with h1 | h3
    · exact exists_sylow_wreath_of_isPSL h1 hW
    · exact exists_sylow_sd_of_isPSL h3 hW
  · rcases hodd with h1 | h3
    · exact exists_sylow_sd_of_isPSU hp2 h1 hW
    · exact exists_sylow_wreath_of_isPSU hp2 h3 hW

end CFSG.Quasithin.H13
