module

public import CFSG.Quasithin.EmptyFaithful.ModHJ4
public import CFSG.Quasithin.EmptyFaithful.ModHM23c

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

theorem input15342SporadicNoM11M22M12HSRuM24HeJ2J4_proved :
    Input15342SporadicNoM11M22M12HSRuM24HeJ2J4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hs
  obtain ⟨s, hsn, hne11, hne22, hne12, hneHS, hneRu, hne24, hneHe, hneJ2, hneJ4, ⟨e⟩⟩ := hs
  rcases hsn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hne11
  · exact absurd rfl hne12
  · exact absurd rfl hne22
  · exact M23c.false_of_m23 c hmin hN hIeq hYL e
  · exact absurd rfl hne24
  · exact absurd rfl hneJ2
  · exact absurd rfl hneJ4
  · exact absurd rfl hneHS
  · exact absurd rfl hneHe
  · exact absurd rfl hneRu

end CFSG.Quasithin.ModH
