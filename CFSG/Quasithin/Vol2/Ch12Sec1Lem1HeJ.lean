module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeD
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeF
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeG
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeH
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeI
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1HeRankSp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Sec1211He

theorem heInspLieTwo_holds
    : HeInspLieTwo := by
  intro X _ _ hX m hm
  rcases hX with ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨-, -, h⟩ |
    ⟨-, -, h⟩⟩ | h
  · exact not_heInspCfg_L2 hf h hm
  · exact not_heInspCfg_L3 hf h hm
  · exact not_heInspCfg_U3 hf h hm
  · exact not_heInspCfg_Sp4 hf h hm
  · exact not_heInspCfg_G2 hf h hm
  · exact not_heInspCfg_D4 hf h hm
  · exact not_heInspCfg_F4 h hm
  · exact not_heInspCfg_Sz h hm
  · exact not_heInspCfg_Tits h hm

theorem lem1211HeInsp_of_remaining
    (hEight : HeInspRankEight) (hE64 : HeInspE64) (hRu : HeInspRu) (hJ4 : HeInspJ4) :
    Lem1211HeInsp :=
  lem1211HeInsp_of heInspRankAlt_holds heInspRankOdd_holds heInspRankSpor_holds hEight hE64 hRu
    hJ4 heInspLieTwo_holds

end Sec1211He

end CFSG.Quasithin.H13
