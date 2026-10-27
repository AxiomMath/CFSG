module

public import CFSG.Quasithin.H13.L32ARuTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L32A

theorem isTypeRu_of_inputs (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h1433 : Lemma1433Five) (h63 : Thm14_7_63) (h72 : Lemma14_7_72) (h73 : Lemma14_7_73)
    (h74 : Lemma14_7_74) {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (h : Hyp147 G T L V) : RuType.IsTypeRu G := by
  have hT := h.fsu.sylow
  exact ⟨L, ruOne_of_inputs h13322 hMod h1433 h72 h74 h, hT.1.toSylow hT.2,
    ruTwo_of_inputs h13322 hMod h63 h72 h73 h74 h _ (IsPGroup.toSylow_coe _ _)⟩

theorem stmt14_7_75_of_inputs (hJ11 : RuType.StatementJ11) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) (h1433 : Lemma1433Five) (h63 : Thm14_7_63) (h72 : Lemma14_7_72)
    (h73 : Lemma14_7_73) (h74 : Lemma14_7_74) : Stmt14_7_75 := by
  intro G _ _ T L V hyp hF hU
  exact hJ11 G (isTypeRu_of_inputs h13322 hMod h1433 h63 h72 h73 h74 ⟨hyp, hF, hU⟩)

end L32A

end CFSG.Quasithin.H13
