module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputs2
public import CFSG.Quasithin.Vol2.Ch4Sec4Rem442

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Quasithin.H13

theorem rem4_4_2_of (h443 : Stmt4_4_3Orbit') : TmpL4_4_2 := by
  intro G _ _ T M L B V hs hnab hK hT hM hTM hL hLf hLM hq hLn hVLT hV hVL hV1 hBMV hB1 hBc hBo
  exact stmt4_4_3Orbit_iff'.1 h443 G T M L B ⊥ V (remark_4_4_2 hs hnab hK hT hM hTM hL hLf hLM hq
    hLn hVLT hV hVL hV1 (hBMV.trans inf_le_left) (hBMV.trans inf_le_right) hB1 hBc hBo)

end CFSG.Quasithin.Vol2.Ch11
