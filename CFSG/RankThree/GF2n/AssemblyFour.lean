module

public import CFSG.RankThree.GF2n.Assembly
public import CFSG.RankThree.GF2n.Tim78Reduction
public import CFSG.GF2Type.DispatchCharTwo
public import CFSG.GF2Type.Aschbacher1976Full.Final
public import CFSG.GF2Type.Aschbacher1977.Main
public import CFSG.GF2Type.Smith1980Orth.Final
public import CFSG.GF2Type.SmithTypeE.Final
public import CFSG.LargeExtraspecial.S14Main
public import CFSG.RankThree.GF2n.Tim78S4Unconditional
public import CFSG.RankThree.GF2n.Smith81.Derivation

public section

namespace CFSG.RankThree.GF2n

open CFSG.GF2Type CFSG.CGT.Timmesfeld75

theorem gf2TypeStatementKP_of_inputs (h76 : Aschbacher1976Statement)
    (h77 : Aschbacher1977WidthAtMostTwoStatement) (h79 : Smith1979StatementCharTwoKP)
    (h80a : Smith1980OrthogonalStatement) (h80b : Smith1980TypeEStatement)
    (hT : CFSG.LargeExtraspecial.Bridge.MainStatement) : GF2TypeStatementKP := by
  intro G _ _ _ hnonab hK hchar t ht hsymp
  exact gf2TypeList_of_inputs_charTwoKP h76 h77 h79 h80a h80b hT hnonab
    (CFSG.GH74.isCharTwoType_iff.mpr hchar)
    (CFSG.ComponentClassification.CatalogueKProper.kProper_of_isKProper hK) ht hsymp

section Node

theorem nodeStatement_proved : NodeStatement :=
  node_final_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩

end Node

section Four

theorem gf2nType_of_four_KP
    (h79 : Smith1979StatementCharTwoKP) (hTim81 : Tim81UnitaryStatement)
    (hSS : StrothSmithStatement) (hTri : Tim78TrichotomyStatement) : GF2nTypeStatement :=
  gf2nType_of_inputs_KP
    (gf2TypeStatementKP_of_inputs
      CFSG.GF2Type.Aschbacher1976Full.aschbacher1976Statement_holds
      CFSG.GF2Type.Aschbacher1977.aschbacher1977WidthAtMostTwo_holds h79
      CFSG.GF2Type.Smith1980Orth.smith1980Orthogonal_holds
      (CFSG.GF2Type.SmithTypeE.smith1980TypeE_of_gh74
        CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
      (CFSG.LargeExtraspecial.S14.mainStatement_of_widthTwo
        CFSG.LargeExtraspecial.S14.aschbacherWidthTwoResidual_holds))
    nodeStatement_proved hTim81 hSS hTri

theorem gf2nType_of_four_sec4
    (h79 : Smith1979StatementCharTwoKP) (hTim81 : Tim81UnitaryStatement)
    (hSS : StrothSmithStatement) (hSec4 : Tim78Sec4Statement) : GF2nTypeStatement :=
  gf2nType_of_four_KP h79 hTim81 hSS (Tim78.tim78Trichotomy_of_sec4 hSec4)

theorem gf2nType_of_three
    (h79 : Smith1979StatementCharTwoKP) (hTim81 : Tim81UnitaryStatement)
    (hSS : StrothSmithStatement) : GF2nTypeStatement :=
  gf2nType_of_four_sec4 h79 hTim81 hSS tim78Sec4_unconditional

theorem gf2nType_of_stroth_smith
    (h79 : Smith1979StatementCharTwoKP)
    (hTim81 : Tim81UnitaryStatement) (hStroth : Stroth80.Stroth1980Statement)
    (hSmith : Smith81.Smith1981Statement) : GF2nTypeStatement :=
  gf2nType_of_three h79 hTim81 (Smith81.strothSmith_of_stroth_smith hStroth hSmith)

end Four

end CFSG.RankThree.GF2n
