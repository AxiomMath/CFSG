module

public import CFSG.Quasithin.EmptyFaithful.S151S8A
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocU33
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocTits
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocD4Model

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin


theorem input15122ThreeCLocB_holds : Input15122ThreeCLocB := by
  intro G _ _ L S hC hS2 hSN hSyl
  rcases hC with hL | hL | hL
  · exact GoldC3.threeCLocConcl_u33 hL hS2 hSN hSyl
  · exact GoldC3.threeCLocConcl_tits hL hS2 hSN hSyl
  · exact GoldC3.threeCLocConcl_3d4 hL hS2 hSN hSyl

end CFSG.Quasithin
