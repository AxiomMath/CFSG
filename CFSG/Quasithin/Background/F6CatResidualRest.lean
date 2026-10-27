module

public import CFSG.Quasithin.Background.F6CatInstancesG22PrimeSylow
public import CFSG.Quasithin.Background.F6CatInstancesG22Shape
public import CFSG.Quasithin.Background.F6CatInstancesAutM12Shape
public import CFSG.Quasithin.Background.F6CatInspectA7
public import CFSG.Quasithin.Background.F6CatInspectS7
public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.Quasithin.Background.F6ResPGammaL2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6CatAssemblyMS2

public section

namespace CFSG.Quasithin

namespace F6

structure F618ResidualRest : Prop where
  goldschmidt : GoldschmidtS3ListCat.{0}
  z2D8List : Z2D8SylowListFact
  wreathIndexTwo : WreathIndexTwoSylowFact
  coverSLEps3 : SLEps3CoverFact
  recogG22M12 : F618RecogG22M12
  recogAutM12 : F618RecogAutM12

theorem f618ResidualInputs_of_rest
    (h : F618ResidualRest) : F618ResidualInputs where
  goldschmidt := h.goldschmidt
  z2D8List := h.z2D8List
  wreathIndexTwo := h.wreathIndexTwo
  l28Aut := l28AutFact_holds
  inspectPGammaL2 := pGammaL2InspectionFact_holds
  coverSLEps3 := h.coverSLEps3
  recogG22M12 := h.recogG22M12
  recogAutM12 := h.recogAutM12
  sylowG22Prime := g22PrimeSylowFact_holds
  shapeG22 := g22AmalgamShapeFact_holds
  shapeM12 := m12AmalgamShapeFact_holds
  shapeAutM12 := autM12AmalgamShapeFact_holds
  inspectPGL2 := pgl2InspectionFact_holds
  inspectA7 := a7InspectionFact_holds
  inspectS7 := s7InspectionFact_holds
  inspectPSigmaL2 := pSigmaL2InspectionFact_holds

end F6

end CFSG.Quasithin
