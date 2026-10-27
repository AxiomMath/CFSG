module

public import CFSG.Quasithin.Background.F6CatResidualRemaining
public import CFSG.Quasithin.Background.GoldschmidtG22SylowIso
public import CFSG.Quasithin.Background.GoldschmidtM12Sylow
public import CFSG.Quasithin.Background.GoldschmidtAutM12

public section

namespace CFSG.Quasithin

namespace F6


theorem f618ResidualRemaining_of_goldschmidt (h : GoldschmidtS3ListCat.{0}) :
    F618ResidualRemaining where
  goldschmidt := h
  z2D8List := z2D8SylowListFact_holds
  coverSLEps3 := slEps3CoverFact_holds
  recogG22M12 := f618RecogG22M12_of_m12SylowList g22SylowIsoM12Fact_holds m12SylowListFact_holds
  recogAutM12 := f618RecogAutM12_holds

end F6

end CFSG.Quasithin
