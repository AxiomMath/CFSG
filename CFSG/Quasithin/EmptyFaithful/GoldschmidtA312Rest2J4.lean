module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.A38c17Rest2

public section

namespace CFSG.Quasithin.A38c17

theorem a312ResidualRest2_of_j4
    (hO : J4Fam.J4OvergroupLocal) (hR : J4Fam.J4M2Residual) : A312ResidualRest2 :=
  ⟨A312U3.su3OddIrr_A38c17_holds, J4Fam.famJ4_of_binders hO hR⟩

end CFSG.Quasithin.A38c17
