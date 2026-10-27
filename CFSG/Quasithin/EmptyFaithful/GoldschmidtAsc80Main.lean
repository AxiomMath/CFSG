module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Eps
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Main

public section

namespace CFSG.Quasithin.E2P.Asc80

open CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique

theorem asc80U3Stmt_of (hirr : CFSG.Quasithin.A312U3.SU3OddIrr) : Asc80U3Stmt :=
  fun _ _ hp2 _ _ _ _ _ _ hK hs hmodel hc hT hsup hM => asc80U3 hirr hp2 hK hs hmodel hc hT hsup hM

theorem asc80L3Eps_holds (hl : SL3OddIrr)
    (hu : CFSG.Quasithin.A312U3.SU3OddIrr) : Asc80L3Eps :=
  asc80L3Eps_of (asc80L3Stmt_of hl) (asc80U3Stmt_of hu)

end CFSG.Quasithin.E2P.Asc80
