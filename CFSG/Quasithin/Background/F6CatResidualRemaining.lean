module

public import CFSG.Quasithin.Background.F6CatResidualRest
public import CFSG.Quasithin.Background.F6W16

public section

namespace CFSG.Quasithin

namespace F6

structure F618ResidualRemaining : Prop where
  goldschmidt : GoldschmidtS3ListCat.{0}
  z2D8List : Z2D8SylowListFact
  coverSLEps3 : SLEps3CoverFact
  recogG22M12 : F618RecogG22M12
  recogAutM12 : F618RecogAutM12

theorem f618ResidualRest_of_remaining
    (h : F618ResidualRemaining) : F618ResidualRest where
  goldschmidt := h.goldschmidt
  z2D8List := h.z2D8List
  wreathIndexTwo := wreathIndexTwoSylowFact_holds
  coverSLEps3 := h.coverSLEps3
  recogG22M12 := h.recogG22M12
  recogAutM12 := h.recogAutM12

end F6

end CFSG.Quasithin
