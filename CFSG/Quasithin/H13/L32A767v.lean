module

public import CFSG.Quasithin.H13.L32A767u
public import CFSG.Quasithin.H13.L32A767c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_67_four_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) (hC137 : U3.C137Statement) : Lemma14_7_67_four := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332) hMod h1222
  have heq : Subgroup.normalizer (kz T V : Set G) = hz T V :=
    le_antisymm (mK_le_hz h hMod h63 h1222 h1332 h1334 hF hC137 h36 h1434)
      (le_normalizer_oTwoUpper _)
  refine ⟨heq, ?_⟩
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    (T_le_hz h h63).trans (le_normalizer_oTwoUpper _)
  have hcc : conjClosure (kz T V) T = kz T V :=
    le_antisymm
      (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.1 (hTK ht) k).1 hk)
      (le_conjClosure (kz T V) T)
  have hU := lemma_1_2_7_three h.fsu.qtke h.fsu.simple h.fsu.nonabelian
    (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) h.fsu.sylow
    (lemma14_7_67_three h h63 h36 h1434)
  rw [hcc, heq] at hU
  exact hU.1.1

theorem lemma14_7_67_of_inputs
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) (hC137 : U3.C137Statement) : Lemma14_7_67 :=
  lemma14_7_67_of h1222 h1332 h63 h36 h1434 (lemma14_7_67_four_of h1222 h1332 h63 h36 h1434 hC137)

end CFSG.Quasithin.H13.L32A
