module

public import CFSG.RankThree.GF2n.Tim81RootCore

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G}

theorem Hyp4.toRootCore (H : Hyp4 M B Q P T) : RootCore M B Q where
  maxLocal := H.maxLocal
  B_le_M := H.B_le_M
  M_le_normalizer_B := H.M_le_normalizer_B
  elemAb := H.elemAb
  ti := H.ti
  B_ne_bot := H.B_ne_bot
  isPGroup_R := H.isPGroup_Q
  M_le_normalizer_R := H.M_le_normalizer_Q
  B_le_R := H.B_le_Q
  center_R := fun hb hx => H.center_Q hb hx
  sq_mem := fun ha => H.sq_mem ha

end CFSG.RankThree.GF2n.Tim78
