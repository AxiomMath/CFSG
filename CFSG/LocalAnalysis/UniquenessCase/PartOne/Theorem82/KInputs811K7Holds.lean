module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedHolds

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K7Omega8Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega8Minus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSp6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem k7Omega8MinusB_holds :
    K7Omega8MinusB := fun _ _ _ _ _ hY _ hp hp5 hpq _ hA h27 =>
  k7b_pomega8m hY hp (by omega) hpq hA h27

theorem k7_holds :
    K7 :=
  k7_of_facts ⟨SignedFacts.sp6K7Facts_holds, SignedFacts.omega7K7Facts_holds,
    SignedFacts.omega8MinusK7Facts_holds, SignedFacts.slK7Facts_holds 6,
    SignedFacts.suK7Facts_holds 6, SignedFacts.slK7Facts_holds 7,
    SignedFacts.suK7Facts_holds 7⟩ k7Omega8MinusB_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
