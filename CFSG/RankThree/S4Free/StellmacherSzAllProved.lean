module

public import CFSG.RankThree.S4Free.Stellmacher34Wire
public import CFSG.LieType.SuzukiSubgroups.Input

public section

namespace CFSG.RankThree.S4Free.Stell34

universe u v

theorem stellmacherSzAll_proved :
    StellmacherSzAll.{u, v} :=
  stellmacherSzAll_holds CFSG.LieType.SuzukiSubgroups.suzukiSubgroupInput_holds

end CFSG.RankThree.S4Free.Stell34
