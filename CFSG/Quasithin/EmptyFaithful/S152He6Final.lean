module

public import CFSG.Quasithin.EmptyFaithful.S152He6Iii
public import CFSG.Quasithin.EmptyFaithful.S152He6AutL2

public section

namespace CFSG.Quasithin

theorem insp15227TransIii_holds : Insp15227TransIii :=
  insp15227TransIii_of_autL2 He6.autL2SylowInner_holds

theorem insp15227TransLn_of_ii (hii : Insp15227TransIi) : Insp15227TransLn :=
  insp15227TransLn_of_parts hii insp15227TransIii_holds

theorem insp15227Shape_of_seven_holds (h7 : Insp15227ShapeSeven) : Insp15227Shape :=
  insp15227Shape_of_seven He6.autL2SylowInner_holds h7

end CFSG.Quasithin
