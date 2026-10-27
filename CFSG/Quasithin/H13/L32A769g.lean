module

public import CFSG.Quasithin.H13.L32A769f
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_69_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h64 : Remark14_7_64) (h674 : Lemma14_7_67_four) (h68 : Lemma14_7_68) : Lemma14_7_69 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  intro G _ _ T L V h γ γ' g k N
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332) hMod h1222
  exact N.relIndex_eq_two h hMod h63 hF h1222 h1332 h1334 h13314 h64 h68 h674

end CFSG.Quasithin.H13.L32A
