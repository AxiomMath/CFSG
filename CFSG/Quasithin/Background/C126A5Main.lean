module

public import CFSG.Quasithin.Background.C126A5Lift10
public import CFSG.Quasithin.Background.C126A5Extract
public import CFSG.Quasithin.Background.C126RadFree
public import CFSG.Quasithin.Background.C126A5Core4

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique B2F E2

theorem a5Stmt_of_radFree (hRF : RadFreeStmt) {G : Type} [Group G] [Finite G]
    {C₁ C₂ : Subgroup G → Subgroup G} : A5Stmt C₁ C₂ := by
  intro hC H T M V hV hmin hSQ hF hred hVZ hJ hA5
  have hRad := hRF G H T M V hV hmin hSQ hF hred hVZ hJ (Or.inr hA5)
  obtain ⟨Y, s, ⟨d⟩⟩ := A5.exists_setting_data hV hmin hSQ hF hred hVZ hJ hRad hA5
  rcases s.dichotomy hC with h | h | ⟨hY, hA3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨x, hxY, hx3, hxL, hxth⟩ := A5.Lift.exists_x (s := s) (d := d)
    exact Or.inr (Or.inr
      (A5.Lift.XData.oneBlock (s := s) (d := d) ⟨hxY, hx3, hxL, hxth⟩ hY.1 hA3 hRad))

end CFSG.Quasithin.C126
