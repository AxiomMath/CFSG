module

public import CFSG.RankThree.GF2n.Tim78S413
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.RankThree.GF2n

open CFSG.RankThree.GF2n.Tim78

section Final

theorem tim78Sec4_of_rootType_step48
    (hRT : ∀ (G : Type) [Group G] [Finite G] (M B Q P T : Subgroup G), Hyp4 M B Q P T →
      RootTypeStep M B)
    (h48 : ∀ (G : Type) [Group G] [Finite G] (M B Q P T : Subgroup G), Hyp4 M B Q P T →
      Step48 M B P T) : Tim78Sec4Statement :=
  tim78Sec4_of_steps
    (fun G _ _ M B Q P T H =>
      (H.tim78_4_10 CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
        (hRT G M B Q P T H) (h48 G M B Q P T H)).2)
    (fun G _ _ M B Q P T H =>
      H.step413 CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
        (hRT G M B Q P T H) (h48 G M B Q P T H))

end Final

end CFSG.RankThree.GF2n
