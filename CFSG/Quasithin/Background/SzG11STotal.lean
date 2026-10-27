module

public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Fourteen
public import CFSG.Quasithin.Background.G10Fifteen
public import CFSG.Quasithin.Background.G116III
public import CFSG.Quasithin.Background.G116II
public import CFSG.Quasithin.Background.E11Main
public import CFSG.Quasithin.Background.G12Four
public import CFSG.Quasithin.Background.G12Main
public import CFSG.Quasithin.Background.G12FourB
public import CFSG.Quasithin.Background.P3OrthoA8Fact
public import CFSG.Quasithin.Background.P3G2
public import CFSG.Quasithin.Background.P3GL24
public import CFSG.Quasithin.Background.P3Sp44
public import CFSG.Quasithin.Background.P4SL34
public import CFSG.Quasithin.Background.P4GLMain
public import CFSG.Quasithin.Background.P4InspectFinal
public import CFSG.Quasithin.Background.G117M22
public import CFSG.Quasithin.Background.SzG11SectionSQT
public import CFSG.Quasithin.Background.SzG11G94Final
public import CFSG.Quasithin.Background.SzG11SAssembly
public import CFSG.Quasithin.Background.SzG11SSeven
public import CFSG.Quasithin.Background.SzG11SG118
public import CFSG.Quasithin.Background.SzG11SNC

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

structure G112InputsS : Prop where
  g93 : G93StmtDimensionOnly
  g115b : G115bStmt
  b49 : B49Stmt
  m12 : NoConfigM12
  om4Minus : NoConfigOm4MinusTwo
  sp4 : NoConfigSp4Two
  g2 : NoConfigG2Two
  tensor : Om4PlusTensor

theorem theoremG112FixS_of_inputs
    (hA21 : AsA21SQTKSection) (h56 : AsB56) (h : G112InputsS) : TheoremG112FixS := by
  have h3 : G1003Stmt := g10_3
  have h4 : G1004Stmt := g10_4 h3 h.b49
  have h5 : G1005Stmt := g10_5 h3 h4
  have h10 : G1010Stmt := g10_10_of_g10_4 h4
  have h11 : G1011Stmt := g10_11 h10
  have h12 : G1012Stmt := g10_12 h11
  have h13 : G1013Stmt := g10_13 h10 h11
  have h1212 : G1212Stmt := g12_12_of_four (g12_1_of_four g12_four_fact) g12_part_four_fact
  have h15 : G1015Stmt :=
    g10_15 h10 h11 h12 h13 h1212 outerGLInput inspect_simple inspect_outer inspect_sylow
      (SzG11.sectionSQTInput_of_asA21 hA21)
  have hApply : G93ApplyStmt := g93_apply h.g93
  have hII : G116IIStmt := g116_II h.g93 outerSL34Input
  have h6 : G116Stmt := g11_6 h15 hII g116_III
  have h7 : G117Stmt :=
    g11_7 hApply e11 h.m12 noConfigL2 (noConfigOm4Minus_of_two h.om4Minus)
      (noConfigSp4_of_two h.sp4) (noConfigG2_of_two h.g2) noConfigOm4Plus
      noConfigOm4PlusFour G117.autHatM22Bound g22DerivedFacts a8OrthogonalFact om4Plus4Iso
  have h8 : G118Stmt := g11_8 h.tensor h7 e11 hApply G118.sp44RankInput G118.gl24SubInput
  have h9 : G119Stmt := g11_9_of_b5 h8 e11 (g10_14 h12) h56
  exact theoremG112S_of_inputs h5 SzG11.g94Stmt_proved h.g115b h6 h8 h9

end SzG11S

end G11

end CFSG.Quasithin
