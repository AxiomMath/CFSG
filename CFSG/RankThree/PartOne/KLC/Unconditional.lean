module

public import CFSG.RankThree.PartOne.KLC.Exceptional
public import CFSG.RankThree.PartOne.KLCE.E6Five
public import CFSG.RankThree.PartOne.KLCE.E8Nine
public import CFSG.RankThree.PartOne.KLCE.E7Five
public import CFSG.RankThree.PartOne.KLCE.E7Eight
public import CFSG.RankThree.PartOne.KLCE.E7Twelve
public import CFSG.RankThree.PartOne.KLCE.TwE6Ten

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exceptionalLayers :
    ExceptionalLayers :=
  ⟨KLCE.layerSector_E6_5, KLCE.layerSector_E7_5, KLCE.layerSector_E7_8, KLCE.layerSector_E7_10,
    KLCE.layerSector_E7_12, KLCE.layerSector_E8_7, KLCE.layerSector_E8_9, KLCE.layerSector_E8_14,
    KLCE.layerSector_E8_18, KLCE.twistedE6TenLayer⟩

theorem lieGoodComponentFixT_exceptional_unconditional
    {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 ∨ t = .twistedF4) :
    LieGoodComponentFixT t := by
  exact lieGoodComponentFixT_exceptional exceptionalLayers ht

end CFSG.RankThree.PartOne.KLC
