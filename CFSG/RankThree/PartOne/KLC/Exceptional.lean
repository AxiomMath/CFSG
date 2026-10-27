module

public import CFSG.RankThree.PartOne.KLC.F4
public import CFSG.RankThree.PartOne.KLC.E7
public import CFSG.RankThree.PartOne.KLC.E8
public import CFSG.RankThree.PartOne.KLC.Tri
public import CFSG.RankThree.PartOne.KLC.TwF4
public import CFSG.RankThree.PartOne.KLC.TwE6

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)


structure ExceptionalLayers : Prop where
  e6_5 : LayerSector Tag.E6 5
  e7_5 : LayerSector Tag.E7 5
  e7_8 : LayerSector Tag.E7 8
  e7_10 : LayerSector Tag.E7 10
  e7_12 : LayerSector Tag.E7 12
  e8_7 : LayerSector Tag.E8 7
  e8_9 : LayerSector Tag.E8 9
  e8_14 : LayerSector Tag.E8 14
  e8_18 : LayerSector Tag.E8 18
  tw_10 : TwistedE6TenLayer

theorem lieGoodComponentFixT_exceptional
    (hL : ExceptionalLayers) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 ∨ t = .twistedF4) :
    LieGoodComponentFixT t := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lieGoodComponentFixT_G2
  · exact lieGoodComponentFixT_F4
  · exact lieGoodComponentFixT_E6_of_layers hL.e6_5
  · exact lieGoodComponentFixT_E7_of_layers hL.e7_5 hL.e7_8 hL.e7_10 hL.e7_12
  · exact lieGoodComponentFixT_E8_of_layers hL.e8_7 hL.e8_9 hL.e8_14 hL.e8_18
  · exact lieGoodComponentFixT_twistedE6_of_layer hL.tw_10
  · exact lieGoodComponentFixT_trialityD4
  · exact lieGoodComponentFixT_twistedF4

end CFSG.RankThree.PartOne.KLC
