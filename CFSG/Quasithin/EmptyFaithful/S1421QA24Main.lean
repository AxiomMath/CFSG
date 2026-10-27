module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Yin
public import CFSG.Quasithin.EmptyFaithful.S1421QA24C129
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem core3HeOdd_of_inputs
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (hSL2 : A312SL2Fact) : Core3HeOdd := by
  intro G _ _ T M H K1 L M₁ c hc hnq
  by_cases hY : yOfL22 T M ≤ L
  · exact QA24.false_of_y_le hSL2 h36 h37 c hnq hY
  · exact QA24.core3HeOdd_false_of_isSylowTwoOf_rOf h129 h36 h37 c hc hnq
      (S1421.isSylowTwoOf_rOf_inf_of_not_le c hY)

end CFSG.Quasithin
