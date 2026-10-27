module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldHCore
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldBound
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.StandardType.TwE6RootKill

section Core


theorem ggTwE6InnerDiagBound2LInput_of_core (hRK : RootKill) (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) :
    GGTwE6InnerDiagBound2LInput := by
  intro K _ _ n p hn hK hp hpq _
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hpq
    omega
  exact ggInnerDiagBound2L_of_field hn hK hp hp2
    (ggTwE6FieldHCore_of_core hRK h5 h3 h34 hn hK hp hpq le_rfl)

end Core


theorem ggTwE6InnerDiagBound2LInput_of_langDatum (h5 : SubfieldLangDatumFive)
    (h3 : SubfieldLangDatumThree) (h34 : SubfieldLangDatumThreeFour) :
    GGTwE6InnerDiagBound2LInput :=
  ggTwE6InnerDiagBound2LInput_of_core (rootKill_of_ennolaKill_weylKill
      (ennolaKill_of_steps leviSplitStep_holds ennolaSplitStep_holds) weylKill_holds) h5 h3 h34

end CFSG.StandardType.TwE6FieldCore

end
