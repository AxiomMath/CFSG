module

public import CFSG.Quasithin.Vol2.Ch11SecBK3A
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem factNot4213_holds : FactNot4213 := by
  intro _ _ _ _ _ _ _ n hn hX hC
  rcases hC with hC | hO
  · exact factNotSmall443_holds _ n hn hX hC.2.1
  · exact factNotSmall443_holds _ n hn hX (Or.inl ⟨2, le_rfl, hO.2.1⟩)

end CFSG.Quasithin.Vol2.Ch11.SecB
