module

public import CFSG.RankThree.PartOne.S11c.PlaneSU5
public import CFSG.RankThree.PartOne.S11d.PlaneAll

public section

namespace CFSG.RankThree.PartOne

theorem planeCenterP'_holds :
    PlaneCenterP' := by
  intro H _ _ p J A c _ _ hrank hJq _ _ h68 hAN hAe hAcard hcA _ hcC hmain
  exact planeCenterSU5 hrank hJq h68 hAN hAe hAcard hcA hcC hmain

end CFSG.RankThree.PartOne
