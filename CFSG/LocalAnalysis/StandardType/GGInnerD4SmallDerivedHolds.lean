module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

theorem derivedOrderInput_holds :
    S2MathAs51600Small.DerivedOrderInput := by
  intro lab hlab hd
  rcases hd with hB | hG | hF
  · refine largeEvenLabelAll_simple_of_markedModel hlab ?_
    intro R _ I F _ _ hM
    rw [ggMarkedModel_card_b2der hB hM, hB]
    rfl
  · refine largeEvenLabelAll_simple_of_markedModel hlab ?_
    intro R _ I F _ _ hM
    rw [CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der hG hM, hG]
    rfl
  · refine largeEvenLabelAll_simple_of_markedModel hlab ?_
    intro R _ I F _ _ hM
    rw [CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der hF hM, hF]
    rfl

end CFSG.StandardType.GGInnerD4SmallParts

end
