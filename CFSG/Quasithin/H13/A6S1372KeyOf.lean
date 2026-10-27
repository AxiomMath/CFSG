module

public import CFSG.Quasithin.H13.A6S1372Key
public import CFSG.Quasithin.H13.A6S1372L24c
public import CFSG.Quasithin.H13.A6S1372KeyData

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem key13721_of
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13314 : Stmt13_3_14)
    (hLem : Lem1374One) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42) (h1352 : Stmt13_5_2)
    (hAlt : Lem1376AltNat) (h13719 : Lem13719L1K) : Key13721 := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab hna
  have : IsMulCommutative ↥(conjClosure S.V3 S.G1) := hab.1
  obtain ⟨C⟩ := S.exists_conf hNS h13315 h1356two hG1 hab hna
  obtain ⟨B, K, hK⟩ :=
    C.exists_KData hNS h13315 h1356two hG1 hab hhat hNU hna h13314 hLem h56 h51 h42
  exact ⟨K, hK.2.2.1, hK.key_data hNS h13315 h1356two hG1 hhat hNU hna h13314 hLem h1352 h51
    hAlt hab (hK.not_L24 hNS h13315 h1356two hG1 hhat hNU hna h13314 hLem h1352 h51 h13719 hab)⟩

end CFSG.Quasithin.H13.A6
