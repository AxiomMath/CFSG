module

public import CFSG.Quasithin.EmptyFaithful.T1515C6Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Construction1516SixFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Ce15Six T Mc M 5 →
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂

theorem construction1516Six_of (h15 : StageLemma1515) (h19 : StageLemma1519)
    (h110 : StageLemma15110) (h113 : StageLemma15113) (h5 : Construction1516SixFive) :
    Construction1516Six := by
  intro G _ _ T Mc M hq hM hCE ⟨p, hp, h6⟩
  rcases hp with rfl | rfl
  · exact exists_setting_six3 hq hM h6 (h15 G T Mc M hq hM) (h19 G T Mc M hq hM hCE)
      (h110 G T Mc M hq hM hCE h6) (h113 G T Mc M hq hM hCE).four
  · exact h5 G T Mc M hq hM hCE h6

end CFSG.Quasithin
