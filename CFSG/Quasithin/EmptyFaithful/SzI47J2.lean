module

public import CFSG.Quasithin.EmptyFaithful.SzI47Stubs
public import CFSG.Quasithin.EmptyFaithful.SzI47J2M
public import CFSG.Quasithin.EmptyFaithful.SzI47J2TofZ
public import CFSG.Quasithin.EmptyFaithful.SzI47J2TofT
public import CFSG.Quasithin.EmptyFaithful.SzI47J2NoA4
public import CFSG.Quasithin.EmptyFaithful.SzI47J2Config

public section

namespace CFSG.Quasithin

theorem j2Recognition_holds :
    J2Recognition :=
  j2Recognition_of_five j2KernelAlt_holds j2KernelComplementExists_holds
    (j2CardAlt4_of_counts j2PairCountZ_holds j2PairCountT_holds) j2CardNe51840_holds
    j2ConfigOfAlt5_holds

theorem i47_of_i47J3
    (h3 : I47J3) : I47Statement :=
  i47_of_j2Recognition j2Recognition_holds h3

end CFSG.Quasithin
