module

public import CFSG.RankThree.PartOne.U5K.Main
public import CFSG.RankThree.PartOne.U5K.Hyp.Transport
public import CFSG.RankThree.PartOne.S12.Sec153Inn

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG

theorem u5EInndiag_of (hMod : KFU5Mod) (hAt : KFU5At) (h5 : U5FiveInndiag) : U5EInndiag := by
  intro G _ _ p A c L E h15 hF12 hout f hf e x hx hxE
  refine ⟨?_, Sec153.u5_faithful_of hMod hAt G p A c L E h15 hF12 hout f e x hx hxE⟩
  by_cases hp5 : p = 5
  · exact h5 G p A c L E h15 hF12 hout hp5 f e x hx hxE
  · obtain ⟨z, hz⟩ := Sec153.u5_act_inner_of_ne_five hMod hAt G p A c L E h15 hF12 hout hp5 f e x
      hx hxE
    rw [hz]
    exact U5Inn_le_U5Inndiag f hf ⟨z, rfl⟩

theorem kf1515U5Faithful_final (h1511 : Node1511) (hMod : KFU5Mod) (hAt : KFU5At)
    (h5 : U5FiveInndiag) : KF1515U5Faithful :=
  kf1515U5Faithful_of h1511 (u5EInndiag_of hMod hAt h5) u5Model

theorem kf1515U5Syl_final (h1511 : Node1511) (hMod : KFU5Mod) (hAt : KFU5At)
    (h5 : U5FiveInndiag) : KF1515U5Syl :=
  kf1515U5Syl_of h1511 (u5EInndiag_of hMod hAt h5) u5Model

theorem kf1515U5Core_final (h1510 : Node1510) (h1511 : Node1511) (hMod : KFU5Mod)
    (hAt : KFU5At) (h5 : U5FiveInndiag) : KF1515U5Core :=
  kf1515U5Core_of h1510 h1511 (u5EInndiag_of hMod hAt h5) u5Model

end CFSG.RankThree.PartOne.U5K
