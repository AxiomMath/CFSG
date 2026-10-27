module

public import CFSG.Quasithin.H13.L32A767b
public import CFSG.Quasithin.H13.U3L134
public import CFSG.Quasithin.H13.L32A767a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_67_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) (h674 : Lemma14_7_67_four) : Lemma14_7_67 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332)
      (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨h1, h2, h5⟩ := lemma14_7_67_one_two_five h h1222 h1332 h1334 h63 hF
  exact ⟨h1, h2, lemma14_7_67_three h h63 h36 h1434, h674 G T L V h, h5⟩

end CFSG.Quasithin.H13.L32A
