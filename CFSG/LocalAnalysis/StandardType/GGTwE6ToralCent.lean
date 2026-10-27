module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcTags

public section

namespace CFSG.StandardType

namespace TwE6Toral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F

variable {K : Type} [Field K] {σ : K →+* K}

theorem graphFixedRootGroup_le_adjointGroup :
    graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K := fun _ hg =>
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).mp
    (graphFixedRootGroup_le TwistTag.E6 K σ hg)).1

end TwE6Toral

end CFSG.StandardType
