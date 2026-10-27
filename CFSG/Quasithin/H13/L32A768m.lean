module

public import CFSG.Quasithin.H13.L32A768l
public import CFSG.Quasithin.H13.KGFact1468G24
public import CFSG.Quasithin.H13.L32A768k
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_68_b_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h36 : A36ForSQTK) (h1434 : Lemma1434One) (h674 : Lemma14_7_67_four)
    (hlist : Lemma115_3_List) (hIdent : KG1468Ident) (hTwoRu : KG1468TwoRu)
    (hBlocks : KG1468Blocks) (h68q : Lemma14_7_68_quasi) : Lemma14_7_68_b := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  intro G _ _ T L V h u hu hu1 hT hS I hI hIn hKI
  by_contra hne
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332) hMod h1222
  have C : Ctx764 G T L V := ⟨h, hMod, h63, hF, h1222, h1332, h1334⟩
  have hR3 : ∀ w ∈ u0 T V, w ≠ 1 → T ≤ Subgroup.centralizer ({w} : Set G) →
      Subgroup.centralizer ({w} : Set G) ≤ hz T V := fun w hw hw1 hTw =>
    centralizer_le_hz_of_le_centralizer h hMod h63 h36 h1434 h674 hw hw1 hTw
  by_cases hq : CFSG.IsQuasisimple ↥I
  · exact C.false_of_quasisimple h13314 hIdent hTwoRu hlist hR3 hu hu1 hT hS hI hIn hKI hne hq
  · exact C.false_of_not_quasisimple h13314 h674 hBlocks h68q hu hu1 hT hS hI hIn hKI hne hq

theorem lemma14_7_68_b_of_inputs
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h36 : A36ForSQTK) (h1434 : Lemma1434One) (h674 : Lemma14_7_67_four)
    (hlist : Lemma115_3_List) (hTwoRu : KG1468TwoRu) (hBlocks : KG1468Blocks)
    (h68q : Lemma14_7_68_quasi) : Lemma14_7_68_b :=
  lemma14_7_68_b_of h1222 h1332 h13314 h63 h36 h1434 h674 hlist KG1468.kg1468Ident_holds hTwoRu
    hBlocks h68q

end CFSG.Quasithin.H13.L32A
