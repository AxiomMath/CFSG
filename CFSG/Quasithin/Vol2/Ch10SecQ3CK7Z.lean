module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7C
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK7K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem b0KA7_of
    (hFF : FactA7FFFix) (h318 : A318Facts) (h36' : A36ForSQTK) (hF6 : FactBenderOver)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (h1021 : Stmt10_2_1) (h1022 : Stmt10_2_2)
    (hE22 : E2.E22StatementC) (he23 : E2.E23Statement) (hAS : Ch11.SecH.AS_I_1_3_L2) :
    B0KA7 := by
  intro G _ _ T L I H K M₁ J n m cfg hc
  rcases Nat.even_or_odd n with hn | hn
  · exact (C11AmS.K7.false_of_even hFF h318 h36' hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22
      he23 hAS cfg hc hn).elim
  · exact C11AmS.K7.b0_le_normalizer_of_odd hF6 h37 h38 h322 h331 h1013 h1021 h1022 hE22 he23 hAS
      cfg hc hn

end CFSG.Quasithin.Vol2.Ch10.SecB
