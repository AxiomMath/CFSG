module

public import CFSG.Quasithin.EmptyFaithful.R3c17H
public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4G

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c10
  CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15

theorem input15335CloseLieRest9_proved (h113 : StageLemma14113) : Input15335CloseLieRest9 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  obtain ⟨f, hf, h⟩ := hRest
  exact SzN27.cl15335_of_sp4 h113 c hN hYL hf h

theorem input15335CloseLieRest_proved
    (h113 : StageLemma14113) : R3c10.Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest9 h113 (input15335CloseLieRest9_proved h113)

end CFSG.Quasithin.R3c17
