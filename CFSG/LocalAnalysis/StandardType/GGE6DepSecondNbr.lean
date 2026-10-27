module

public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepStdSubMulPoint
public import CFSG.LocalAnalysis.StandardType.GGE6DepNbrOfBlocks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE6DepSecondNbr_of_blockCfg (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hb : GGE6DepBlockCfgInput) : GGE6DepSecondNbr := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hK hE
  obtain ⟨hD, hvx, hvy⟩ := ggStdSub_mul_point hcfg hK
  exact ⟨x * y, _, ggNbr_of_blocks hL hP hcfg hinn.1 hD
    (hb G p B Bs x L D J hcfg hop hinn hnt y K hK hE), hvx, hvy⟩

theorem ggE6DepPerpExcl_of_secondNbr (h2 : GGE6DepSecondNbr) (hpin : GGE6DepNbrPin) :
    GGE6DepPerpExcl := by
  intro G _ _ p B Bs x L D J hcfg hop hinn hnt y K hK hE
  obtain ⟨v, X, hX, -, hvy⟩ := h2 G p B Bs x L D J hcfg hop hinn hnt y K hK hE
  exact hvy (hpin G p B Bs x L D J hcfg hop hinn hnt y K hK hE v X hX)

theorem ggE6DepPerpExcl_of_blockCfg (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hb : GGE6DepBlockCfgInput) (hpin : GGE6DepNbrPin) : GGE6DepPerpExcl :=
  ggE6DepPerpExcl_of_secondNbr (ggE6DepSecondNbr_of_blockCfg hL hP hb) hpin

end CFSG.StandardType

end
