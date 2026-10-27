
module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.A1cA133Two

public section

namespace CFSG.Quasithin

theorem a130Fact : A130Fact := fun p hp hp4 P _ hP f => by
  have := Fact.mk hp
  exact not_injective_sl2_of_mulEquiv (p := p) hP hp4 f

theorem a133TwoFact : A133TwoFact := fun p hp hp4 L _ _ P _ hP hL => by
  have := Fact.mk hp
  exact two_lt_pRank_of_quotient_sl2 hp4 P hP hL

theorem A36CaseBFacts.of_proved (h129 : A129One) (hl2 : L2MultiplierFact) : A36CaseBFacts where
  a129 := h129
  a130 := a130Fact
  a133 := a133TwoFact
  l2mult := hl2

end CFSG.Quasithin
