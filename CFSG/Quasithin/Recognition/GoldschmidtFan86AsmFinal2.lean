module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmI3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmT
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresTree
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Final

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

theorem fanTreeMain_proved' :
    FanTreeMain :=
  fanTreeMain_of_fanTail AsmI3.fanTailInputs_proved fanTail_proved

theorem hayashiFiveThree_proved' :
    HayashiFiveThree :=
  hayashiFiveThree_of_fanTreeMain fanTreeMain_proved'

end CFSG.Quasithin.Fan86
