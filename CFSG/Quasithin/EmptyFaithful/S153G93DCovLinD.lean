module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinB
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinC
public import CFSG.Quasithin.EmptyFaithful.S153G93DCases

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovLin

theorem covSL3_holds : CovSL3 := by
  intro W _ _ J n h
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_natCard_eq hK
  exact covOrder3_of_realizes hreal fun v hv => exists_sl3_order_three_fixing hv

theorem covSp4_holds : CovSp4 := by
  intro W _ _ J n h
  obtain ⟨K, _, _, hK, hreal⟩ := h
  have : CharP K 2 := charP_two_of_natCard_eq hK
  exact covOrder3_of_realizes hreal fun v hv => exists_sp4_order_three_fixing hv

end CovLin

end S153G93D

end CFSG.Quasithin
