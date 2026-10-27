module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsMuT
public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsFixBC
public import CFSG.Quasithin.Recognition.Stroth.Str83G5Goal
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithHolds

public section

namespace CFSG.Quasithin.Stroth.G5

theorem str83G5AbstractGoal_holds :
    Str83G5AbstractGoal := by
  intro G _ _ n c
  obtain ⟨μT, hμT, h1, h2, hdim⟩ := c.exists_muT
  obtain ⟨l, hl, hμ⟩ := c.exists_ySeries_Q₁ hμT
  exact c.win_zero_seven_eq_bot (str83G5ArithGoal_holds n c.odd c.three_le c.k₀ c.m₀
    c.isUnit_k₀ c.isUnit_m₀ c.pattern c.pattern_admissible c.pass μT h1 h2 hdim
    (c.fst_eq_zero_or_isUnit hl hμ) (c.four_dvd_card_filter_ne_zero hl hμ)
    (c.four_dvd_card_filter_psi hl hμ))

end CFSG.Quasithin.Stroth.G5

end
