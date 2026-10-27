module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelTits
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelTwoF4

public section

namespace CFSG.Quasithin.Fan86

theorem modelFacts :
    ModelFacts :=
  ⟨Model.modelFacts_tits, Model.modelFacts_twoF4⟩

end CFSG.Quasithin.Fan86
