module

public import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6
public import CFSG.RankThree.PartTwo.Census.Exceptional.TrialityD4
public import CFSG.RankThree.PartTwo.Census.Exceptional.ReeG2
public import CFSG.RankThree.PartTwo.Census.CarrierCases
public import CFSG.RankThree.PartOne.Census3.OpenCases

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open TauCeti

@[expose] def RankFourReeG2 : Prop :=
  ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), 2 ≤ m →
    ∀ [Finite (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group],
      4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group

theorem exceptionalWitnessCases433_of_reeG2 (hR : RankFourReeG2) :
    ExceptionalWitnessCases433 where
  e6 := four_le_twoLocalOddRank_E6
  e7 := four_le_twoLocalOddRank_E7
  e8 := four_le_twoLocalOddRank_E8
  twistedE6 := four_le_twoLocalOddRank_twistedE6
  f4 q hv hq _ := four_le_twoLocalOddRank_F4 q hv hq
  g2 q hv hp hf _ := four_le_twoLocalOddRank_G2 q hv hp hf
  trialityD4 q hv hp _ := four_le_twoLocalOddRank_trialityD4 q hv hp
  reeG2 := hR

theorem exceptionalRankFour_of_reeG2 (hR : RankFourReeG2) :
    CFSG.RankThree.PartOne.Census3.ExceptionalRankFour where
  e6 := four_le_twoLocalOddRank_E6
  e7 := four_le_twoLocalOddRank_E7
  e8 := four_le_twoLocalOddRank_E8
  twistedE6 := four_le_twoLocalOddRank_twistedE6
  f4 q hv hq _ := four_le_twoLocalOddRank_F4 q hv hq
  g2 q hv hp hf _ := four_le_twoLocalOddRank_G2 q hv hp hf
  trialityD4 q hv hp _ := four_le_twoLocalOddRank_trialityD4 q hv hp
  reeG2 := hR

theorem rankFourReeG2 : RankFourReeG2 := fun m hv hm _ => four_le_twoLocalOddRank_reeG2 m hv hm

theorem exceptionalWitnessCases433 : ExceptionalWitnessCases433 :=
  exceptionalWitnessCases433_of_reeG2 rankFourReeG2

theorem exceptionalRankFour : CFSG.RankThree.PartOne.Census3.ExceptionalRankFour :=
  exceptionalRankFour_of_reeG2 rankFourReeG2

end CFSG.RankThree.PartTwo.Census.Exceptional
