module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Model
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Assembly

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

theorem hayashiFiveThree_of_fanTreeMain
    (h : FanTreeMain) : HayashiFiveThree :=
  hayashiFiveThree_of_fan (fanMain_of_fanTreeMain h) modelFacts

end CFSG.Quasithin.Fan86
