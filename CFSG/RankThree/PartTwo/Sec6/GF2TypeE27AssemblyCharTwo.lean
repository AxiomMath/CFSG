module

public import CFSG.RankThree.PartTwo.Sec6.LitScopeProof
public import CFSG.GF2Type.DispatchCharTwo
public import CFSG.GF2Type.Aschbacher1977.Main
public import CFSG.GF2Type.Smith1980Orth.Final
public import CFSG.GF2Type.SmithTypeE.Final
public import CFSG.LargeExtraspecial.S14Main
public import CFSG.RankThree.GF2n.Item310Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec6

section Certs

theorem gf2TypeE27_of_inputs''
    (hA76 : CFSG.GF2Type.Aschbacher1976Statement)
    (hS79k : CFSG.GF2Type.Smith1979StatementCharTwoKP) : GF2TypeE27 := by
  intro G _ _ hst t ht _ _ _ _ hsymp
  have := hst.isSimpleGroup
  exact hst.not_inCatalog (CFSG.RankThree.GF2n.item310Bridges.inCatalog_of_gf2TypeList
    (CFSG.GF2Type.gf2TypeList_of_inputs_charTwoKP hA76
      CFSG.GF2Type.Aschbacher1977.aschbacher1977WidthAtMostTwo_holds hS79k
      CFSG.GF2Type.Smith1980Orth.smith1980Orthogonal_holds
      (CFSG.GF2Type.SmithTypeE.smith1980TypeE_of_gh74
        CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
      (CFSG.LargeExtraspecial.S14.mainStatement_of_widthTwo
        CFSG.LargeExtraspecial.S14.aschbacherWidthTwoResidual_holds)
      hst.nonabelian hst.charTwoType hst.kProper ht hsymp))

end Certs

end CFSG.RankThree.PartTwo.Sec6
