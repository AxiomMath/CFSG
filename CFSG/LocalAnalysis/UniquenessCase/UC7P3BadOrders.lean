module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadMembers
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.RankThree.PartOne.K159.AutSzIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding.KFactProofs.SmallIdent

theorem badListOrders_holds :
    BadListOrders :=
  ⟨fun _ _ hs hK => card_of_isMcL hs hK, fun _ _ hs hK => card_of_isJ4 hs hK,
    fun _ _ hs hK => card_of_isFi22 hs hK, fun _ _ hK => card_of_isTitsGroup hK,
    fun _ _ hiso => (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso).card⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
