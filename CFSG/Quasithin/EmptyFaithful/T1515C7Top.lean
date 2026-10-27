module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem construction1516Seven_of (h15 : StageLemma1515) (h19 : StageLemma1519)
    (h113 : StageLemma15113) : Construction1516Seven := by
  intro G _ _ T Mc M hq hM hCE h7
  exact exists_setting_seven hq hM h7 (h15 G T Mc M hq hM) (h19 G T Mc M hq hM hCE)
    (h113 G T Mc M hq hM hCE).four

end CFSG.Quasithin
