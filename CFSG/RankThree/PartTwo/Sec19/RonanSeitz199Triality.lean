module

public import CFSG.RankThree.PartTwo.Sec19.RonanSeitz199
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinal
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families
import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThreeAll
import CFSG.HardMathSupport.Seitz.TrialityEven.Assembly
import CFSG.HardMathSupport.Seitz.TrialityEven.TwoThree

public section

namespace CFSG.RankThree.PartTwo.Sec19.RonanSeitz199

open CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.SeitzGeneration

theorem seitzThreeTrialityWide_of_outerWide
    (h : SeitzExcOuterWideForAt IsTrialityIndex PrimeRange.three) : SeitzThreeTrialityWide := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, ⟨q, rfl⟩, hcase⟩
  rcases hcase with ⟨hout, hns⟩ | ⟨-, hnr⟩
  · exact h ⟨_, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hout, hns, ⟨q, rfl⟩, rfl⟩
  · have hpq : 3 ≠ q.p := by
      intro h3
      apply hpd
      simpa [TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.LieTypeIndex.characteristic_trialityD4] using h3
    exact absurd (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv
      fun h3 => hpq h3.symm) hnr

theorem seitzThreeTrialityWide_of_odd
    (hOdd : ExcWideThree.TrialityThreePlanesOdd) : SeitzThreeTrialityWide :=
  seitzThreeTrialityWide_of_outerWide
    (ExcWideThree.seitzExcOuterWideTriality_three_of_odd_two hOdd seitzThreeTrialityWideTwo_holds)

theorem seitzThreeTriality_of_odd
    (hOdd : ExcWideThree.TrialityThreePlanesOdd) : SeitzThreeTriality :=
  SeitzScopeProof.seitzThreeTriality_of_residuals
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcAnisotropicTrialityThree_of_even
      (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
        CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds))
    CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.seitzExcOuterNarrowTrialityThree_proved
    (seitzThreeTrialityWide_of_odd hOdd)

theorem seitz199_of_trialityOdd
    (hOdd : ExcWideThree.TrialityThreePlanesOdd) : Seitz199 :=
  seitz199_of_seitzThree seitzThreeLThreePi_holds (seitzThreeTriality_of_odd hOdd)
    seitz199Outer_holds

end CFSG.RankThree.PartTwo.Sec19.RonanSeitz199
