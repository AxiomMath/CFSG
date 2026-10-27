module

public import CFSG.Quasithin.EmptyFaithful.S14612DB
public import CFSG.Quasithin.EmptyFaithful.S146P3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem indexThreeP_proved : IndexThreeP := by
  intro G _ _ T M S H PQ p hred hp H₀ H₁ H₂ t h
  subst hp
  exact h.relIndex_eq_two_of_p_three S hred

end CFSG.Quasithin
