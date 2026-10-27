module

public import CFSG.Quasithin.Background.F6CatRecogZ4wrZ2

public section

namespace CFSG.Quasithin

namespace F6

structure F618QSInputsMS2 : Prop where
  theoremC : NativeTheoremCSection
  sqtSection : NativeSQTSection
  walter : WalterModelsStatement
  wreathed : WreathedRecognitionStatement
  goldschmidt : GoldschmidtS3ListCat.{0}
  z2D8List : Z2D8SylowListFact
  wreathIndexTwo : WreathIndexTwoSylowFact
  l28Aut : L28AutFact
  inspectPGammaL2 : PGammaL2InspectionFact
  coverSLEps3 : SLEps3CoverFact
  recogG22M12 : F618RecogG22M12
  recogAutM12 : F618RecogAutM12
  sylowG22Prime : G22PrimeSylowFact
  shapeG22 : G22AmalgamShapeFact
  shapeM12 : M12AmalgamShapeFact
  shapeAutM12 : AutM12AmalgamShapeFact
  inspectPGL2 : PGL2InspectionFact
  inspectA7 : A7InspectionFact
  inspectS7 : S7InspectionFact
  inspectPSigmaL2 : PSigmaL2InspectionFact

theorem F618QSInputsMS2.toF618QSInputsMS
    (I : F618QSInputsMS2) : F618QSInputsMS :=
  ⟨I.theoremC, I.sqtSection, I.goldschmidt,
    f618RecogZ2D8SQT_holds I.walter I.l28Aut I.z2D8List I.inspectPGammaL2,
    f618RecogZ4wrZ2SQT_holds I.walter I.wreathed I.wreathIndexTwo I.inspectPGammaL2
      I.coverSLEps3,
    I.recogG22M12, I.recogAutM12, I.sylowG22Prime, I.shapeG22, I.shapeM12, I.shapeAutM12,
    I.inspectPGL2, I.inspectA7, I.inspectS7, I.inspectPSigmaL2⟩

theorem theoremF618Cat_ofMS2
    (hNQ : F617NonquasisimpleCaseCat) (I : F618QSInputsMS2) :
    TheoremF618Cat :=
  theoremF618Cat_ofMS hNQ I.toF618QSInputsMS

structure F618ResidualInputs : Prop where
  goldschmidt : GoldschmidtS3ListCat.{0}
  z2D8List : Z2D8SylowListFact
  wreathIndexTwo : WreathIndexTwoSylowFact
  l28Aut : L28AutFact
  inspectPGammaL2 : PGammaL2InspectionFact
  coverSLEps3 : SLEps3CoverFact
  recogG22M12 : F618RecogG22M12
  recogAutM12 : F618RecogAutM12
  sylowG22Prime : G22PrimeSylowFact
  shapeG22 : G22AmalgamShapeFact
  shapeM12 : M12AmalgamShapeFact
  shapeAutM12 : AutM12AmalgamShapeFact
  inspectPGL2 : PGL2InspectionFact
  inspectA7 : A7InspectionFact
  inspectS7 : S7InspectionFact
  inspectPSigmaL2 : PSigmaL2InspectionFact

theorem F618ResidualInputs.toF618QSInputsMS2 (hC : NativeTheoremCSection)
    (hQ : NativeSQTSection) (hW : WalterModelsStatement) (hWr : WreathedRecognitionStatement)
    (I : F618ResidualInputs) : F618QSInputsMS2 :=
  ⟨hC, hQ, hW, hWr, I.goldschmidt, I.z2D8List, I.wreathIndexTwo, I.l28Aut, I.inspectPGammaL2,
    I.coverSLEps3, I.recogG22M12, I.recogAutM12, I.sylowG22Prime, I.shapeG22, I.shapeM12,
    I.shapeAutM12, I.inspectPGL2, I.inspectA7, I.inspectS7, I.inspectPSigmaL2⟩

end F6

end CFSG.Quasithin
