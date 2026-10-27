module

public import CFSG.RankThree.PartOne.S11d.PlaneOdd
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.RankThree.PartOne.OutStructure


theorem oddOutGaps : OddOutGaps :=
  ⟨fun _ _ _ _ _ hp hp5 hℓ h => (SpTwo.outPNice_PSp_two_odd hp (by omega) hℓ h).toChain,
    fun _ _ _ _ hp _ h => (outPNice_twistedG2 hp h).toChain⟩

end CFSG.RankThree.PartOne.AUTSL
