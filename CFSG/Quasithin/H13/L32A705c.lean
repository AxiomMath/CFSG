module

public import CFSG.Quasithin.H13.L32A705b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_5_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h13314 : A6.Stmt13_3_14) : Lemma14_7_5 := by
  intro G _ _ T L V H S hN
  have hHL := Setting147.H_le_N_l1 S h1332 hN
  have hF : HypF98 T V L (fsuV1 T V) V H :=
    Setting147.hypF98 S (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334) h1222
  have h2 : pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 H = pCoreOf 2 (l1 T L V ⊔ T) := by
    have := lemma14_7_4_four S hF h1222 h1332 h1334 h13314
    rwa [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at this
  exact ⟨fun γ γ' g s => ⟨Setting147.Dγ_lt_Uγ S hF h1222 h1332 h1334 hHL s,
      Setting147.comm_Uγ_l1 S hF h1332 hHL s⟩, h2,
    Setting147.card_l1_star S h1222 h1332 h1334 hHL, Setting147.R1_star_Q S h2,
    Setting147.R1_star_eq S h1222 h1332 h1334 hHL, Setting147.relIndex_R1_star S h1222 h1332 h1334,
    Setting147.UH_eq S h1222 h1332 h1334 hHL⟩

end CFSG.Quasithin.H13.L32A
