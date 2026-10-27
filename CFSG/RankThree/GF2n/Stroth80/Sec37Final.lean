module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Main
public import CFSG.RankThree.GF2n.Stroth80.Sec37Main
public import CFSG.RankThree.GF2n.Stroth80.Sec37Glue
public import CFSG.RankThree.GF2n.Stroth80.Sec37Ovoid
public import CFSG.RankThree.GF2n.Stroth80.Sec37Module
public import CFSG.RankThree.GF2n.Stroth80.Sec37Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommOdd
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommNormal
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommEleven
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommForm2
public import CFSG.RankThree.GF2n.Stroth80.Sec37Commuting

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem bridge37 : Bridge37Statement := by
  intro G _ _ M Q Z B _ hc K _ _ γ M₀ φ hφ
  exact hc.bar_Lgen_equiv φ hφ

theorem stroth37Statement_of_inputs (h34 : Stroth34Statement)
    (hHKS : HKSNormalStatement) (hSL2 : SL2FixedLineDimStatement)
    (hCom : Stroth37CommutingStatement) : Stroth37Statement :=
  stroth37Statement_of_geom h34 (geom37 h34 hHKS hSL2 ovoid37 module37 bridge37) hCom

theorem hksStatement_of_normal (h : HKSNormalStatement) : HKSStatement := by
  intro H _ _ Ω _ _ _ m hm hcard h2 α R hR hRn hRe hreg
  obtain ⟨L, hLn, hLs, hLiso, hL2, -⟩ := h H Ω m hm hcard h2 α R hR hRn hRe hreg
  exact ⟨L, hLn, hLs, hLiso, hL2⟩

theorem stroth37Commuting_of_inputs
    (h34 : Stroth34Statement)
    (hF2 : CFSG.LargeExtraspecial.S4.Form2StrongStmt) : Stroth37CommutingStatement :=
  Tim37.stroth37Commuting_of_dichotomy h34
    (Tim37.form2Dichotomy_of_lifts Tim37.oddCentralLift Tim37.normalLift) Tim37.eleven37 hF2

theorem stroth37Statement_of_form2
    (h34 : Stroth34Statement)
    (hF2 : CFSG.LargeExtraspecial.S4.Form2StrongStmt) (hHKS : HKSNormalStatement)
    (hSL2 : SL2FixedLineDimStatement) : Stroth37Statement :=
  stroth37Statement_of_inputs h34 hHKS hSL2 (stroth37Commuting_of_inputs h34 hF2)

theorem stroth37Statement_of_classical_inputs
    (hT75 : TimmesfeldTransitivityTI) (hF2 : CFSG.LargeExtraspecial.S4.Form2StrongStmt)
    (hHKS : HKSNormalStatement) (hSL2 : SL2ModuleDimStatement)
    (hSLfix : SL2FixedLineDimStatement) (hB : Stroth34CaseBStatement) : Stroth37Statement :=
  stroth37Statement_of_form2
    (stroth34Statement_of_inputs hT75 (hksStatement_of_normal hHKS) hSL2 hB) hF2 hHKS hSLfix

end CFSG.RankThree.GF2n.Stroth80
