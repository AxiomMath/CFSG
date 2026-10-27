module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldHCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.StandardType.TwE6RootKill

section Core


theorem ggTwE6ThreeFieldInput_of_core (hRK : RootKill) (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) :
    GGTwE6ThreeFieldInput := by
  intro K _ _ n hn hK h3q
  exact ggTwE6FieldHCore_of_core hRK h5 h3 h34 hn hK Nat.prime_three h3q
    (by decide : TwE6Delta.liftRank 3 ≤ 4)

end Core


theorem ggTwE6ThreeFieldInput_of_langDatum (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) : GGTwE6ThreeFieldInput :=
  ggTwE6ThreeFieldInput_of_core (rootKill_of_ennolaKill_weylKill
      (ennolaKill_of_steps leviSplitStep_holds ennolaSplitStep_holds) weylKill_holds) h5 h3 h34

end CFSG.StandardType.TwE6FieldCore

end
