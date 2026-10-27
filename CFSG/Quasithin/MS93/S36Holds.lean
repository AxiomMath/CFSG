module

public import CFSG.Quasithin.MS93.S36
public import CFSG.Quasithin.MS93.S36Sp
public import CFSG.Quasithin.MS93.S36SpE
public import CFSG.Quasithin.MS93.S32
public import CFSG.Quasithin.MS93.S33LamF
public import CFSG.Quasithin.MS93.S33BadG2

public section

namespace CFSG.Quasithin.MS93

theorem s36Sp4Excl_holds :
    S36Sp4Excl :=
  s36Sp4Excl_of_end s32_holds S36SP.s36SpEnd_holds

theorem s36_of_s38
    (h38 : S38) : S36 :=
  s36_of s32_holds (S33.s33w_of_bad s32_holds h38 S33.s33Bad_holds) s36Sp4Excl_holds

end CFSG.Quasithin.MS93
