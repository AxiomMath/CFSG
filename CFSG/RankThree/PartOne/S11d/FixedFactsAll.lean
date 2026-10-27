module

public import CFSG.RankThree.PartOne.S11d.FixedFactsPSL
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSU
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSp
public import CFSG.RankThree.PartOne.S11d.FixedFactsOrth
public import CFSG.RankThree.PartOne.S11d.FixedFactsE6
public import CFSG.RankThree.PartOne.S11d.FixedFactsE6Tw
public import CFSG.RankThree.PartOne.S11d.FixedFactsTri
public import CFSG.RankThree.PartOne.S11d.FixedFactsSz
public import CFSG.RankThree.PartOne.S11d.FixedFactsRee

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG.Assembly.LowTwoRank (StatedLieTag)


theorem tagFixedFacts_all (hNL : ChevalleySubfieldNonLocalized)
    (hTits : LargeReeTitsNonLocalized) : ∀ t, TagFixedFacts t := by
  intro t
  cases t
  · exact tagFixedFacts_PSL
  · exact tagFixedFacts_PSU
  · exact tagFixedFacts_PSp
  · exact tagFixedFacts_POmegaOdd
  · exact tagFixedFacts_POmegaPlus
  · exact tagFixedFacts_POmegaMinus
  · exact tagFixedFacts_G2 hNL
  · exact tagFixedFacts_F4 hNL
  · exact tagFixedFacts_E6 hNL
  · exact tagFixedFacts_E7 hNL
  · exact tagFixedFacts_E8 hNL
  · exact tagFixedFacts_twistedE6
  · exact tagFixedFacts_trialityD4
  · exact tagFixedFacts_Sz
  · exact tagFixedFacts_twistedG2
  · exact tagFixedFacts_twistedF4 hTits
  · exact tagFixedFacts_Tits

end CFSG.RankThree.PartOne.FieldFix
