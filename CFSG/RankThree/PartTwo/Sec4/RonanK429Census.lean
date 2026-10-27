module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Census
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Census

theorem item4_29Outer_of_rows (R : K429Rows) : Item4_29Outer := by
  intro G _ _ hG hθ hE A hA c hc hc1 L hL hAN hAC hLc K hK K' hK' htype hcent
  have hq : IsQuasisimple L := hL.1
  have hlist := RonanK432.list42_quotient_center hq (sectionFourHyp_subgroup hG L)
  exact R.row_of_list42 hq.2.1 hq.2.2 hlist G hG hθ hE A hA c hc hc1 L hL ⟨MulEquiv.refl _⟩ hAN hAC
    hLc K hK K' hK' htype hcent

end Census

end CFSG.RankThree.PartTwo.Sec4.RonanK429
