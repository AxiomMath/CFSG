module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TwE6_pow_six_le_card (hB : GGTwE6ThreeBstarRankInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hmark : GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs L) : p ^ 6 ≤ Nat.card Bs := by
  have hm := hmark
  obtain ⟨-, lab, -, hraw⟩ := hm
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hp3, -⟩, -, hBsN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hγ := hB G p B Bs x L D J hcfg hmark hBsN
  obtain ⟨hpr, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hpr hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hBsN
  subst hp3
  calc 3 ^ 6 = 3 ^ 5 * 3 := by norm_num
    _ ≤ Nat.card (ggGamma L hBsN).range * 3 := Nat.mul_le_mul_right 3 hγ
    _ = Nat.card Bs := hmul

end CFSG.StandardType

end
