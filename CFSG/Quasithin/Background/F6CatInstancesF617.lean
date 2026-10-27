module

public import CFSG.Quasithin.Background.F6NQAssembly
public import CFSG.Quasithin.Background.F6CatAssemblyMS2
public import CFSG.Quasithin.Background.F6CatInstances
public import CFSG.Quasithin.Background.F6CatInstancesSQT
public import CFSG.Quasithin.Background.F6CatInstancesWalter
public import CFSG.Quasithin.Background.F6CatInstancesWreathed

public section

namespace CFSG.Quasithin

namespace F6

theorem f617NonquasisimpleCaseCat_of_F613Two
    (hF : F613Two.{0}) : F617NonquasisimpleCaseCat :=
  f617NonquasisimpleCaseCat_of hF nativeSQTSection walterModelsStatement

theorem theoremF618Cat_of_F613Two
    (hF : F613Two.{0}) (I : F618ResidualInputs) :
    TheoremF618Cat :=
  theoremF618Cat_ofMS2 (f617NonquasisimpleCaseCat_of_F613Two hF)
      (I.toF618QSInputsMS2 nativeTheoremCSection nativeSQTSection walterModelsStatement
          wreathedRecognitionStatement)

end F6

end CFSG.Quasithin
