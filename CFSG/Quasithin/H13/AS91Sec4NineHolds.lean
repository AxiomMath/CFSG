module

public import CFSG.Quasithin.H13.AS91Sec4Nine
public import CFSG.Quasithin.Background.HM22Out
public import CFSG.CGT.M24S.Main

public section

namespace CFSG.Quasithin.H13.AS91

theorem stmt4_9_holds :
    Stmt4_9 :=
  stmt4_9_of CFSG.Quasithin.hatM22SmallModules_holds
    CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Out_holds
    CFSG.Quasithin.H.Mathieu.M22Link.kg82HatM22Twelve_holds
    CFSG.CGT.M24S.m24SylowInput CFSG.Quasithin.mathieuSmallIrr24_holds

end CFSG.Quasithin.H13.AS91
