module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem construction1516Four_of (h15 : StageLemma1515) (h17 : StageLemma1517)
    (h19 : StageLemma1519) (h113 : StageLemma15113) : Construction1516Four := by
  intro G _ _ T Mc M hq hM hCE h4
  exact exists_setting_four hq hM h4 (h15 G T Mc M hq hM) (h17 G T Mc M hq hM hCE)
    (h19 G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four

end CFSG.Quasithin
