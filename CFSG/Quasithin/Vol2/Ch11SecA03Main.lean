module

public import CFSG.Quasithin.Vol2.Ch11SecA03Two
public import CFSG.Quasithin.Vol2.Ch11SecA03Five

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

theorem stmt11_0_3_of (h322 : Ch10.TmpL6_3_2_2_two) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h324 : TmpL6_3_2_2_four) (h326 : TmpL6_3_2_2_six) (h325 : Stmt3_2_5)
    (h16 : ASInputs.AS_I_1_6) (h331 : Stmt3_3_1) (h51 : AsB51) (h56 : AsB56)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (hTw : FactTwist) (hKF : SecC.KindModuleFacts)
    (hFC : SecB.FactCentralizerTwo) (h1102 : Stmt11_0_2) : Stmt11_0_3 := by
  intro G _ _ T L I n h
  exact ⟨stmt11_0_3_one h322 h, stmt11_0_3_two hTw h325 h1102 h324 h,
    stmt11_0_3_three h325 h1102 h324 h326 h16 h331 h, isTISetIn_fsuV h325 h,
    stmt11_0_3_five h51 h56 hKF h322 h3228 hC58 h317 hFC h325 h331 h1102 h⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
