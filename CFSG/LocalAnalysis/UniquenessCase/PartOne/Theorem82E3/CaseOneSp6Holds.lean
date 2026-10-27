module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Final
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1CoverHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsOmega8Minus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFactsSp6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K7Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLiePlanes
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLieSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLieWeight3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

section


theorem Case811Sylow.sp6Excluded_holds {c : Ctx82E3 D} (h : Case811Sylow c) :
    h.Sp6Excluded :=
  h.sp6Excluded_of_inputs (Theorem82.k6c_of_facts
      ⟨Theorem82.SignedFacts.sp6K6cFacts_holds, Theorem82.SignedFacts.omega7K6cFacts_holds,
          Theorem82.SignedFacts.omega8MinusK6cFacts_holds, Theorem82.SignedFacts.slK6cFacts_holds 6,
          Theorem82.SignedFacts.suK6cFacts_holds 6, Theorem82.SignedFacts.slK6cFacts_holds 7,
          Theorem82.SignedFacts.suK6cFacts_holds 7⟩) Theorem82.k7_holds k7Sp6Planes_holds
    k7Sp6Weight3_holds sp6SylowWreath_holds UC22.InS3.UC326.k326P2S_holds

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
