module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseSpor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseTits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

section StepOne


theorem phase45_pRank_five_le_one (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hK1a : K45CharTwoNormal) (hK1b : K45CharTwoBorelGen) (hK2 : K45WeylFive) {X : Type}
    [Group X] [Finite X] {L A₁ A₂ B T ML : Subgroup X} (hc : PhaseConfig45 L A₁ A₂ B T ML) :
    CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ 1 := by
  by_contra hle
  have hpos : 0 < CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) := by
    have := not_le.mp hle
    omega
  have h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) := by
    have := not_le.mp hle
    omega
  have h5dvd : 5 ∣ Nat.card L :=
    CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos 5
      (⊤ : Subgroup ↥L) hpos
  have hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 (ML.subgroupOf L) := hc.hC6 h5dvd
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hc.hLnab (isMulCommutative_iff.mpr h)
  rcases phase45_identify_five hId hLie hCyc hc.hLs hnab hc.hLK h2 hM with
    hAlt | ⟨s, hSpor⟩ | ⟨d, hLieD, hcases⟩
  · obtain ⟨e⟩ := hAlt
    exact phase45_false_of_alternating hc.hLn hc.hLs hc.hLnab hc.hCL e hc.hA1 hc.hA2
      hc.hA12 hc.hA12c hc.hT hc.hAT hc.hTL
  · obtain ⟨e⟩ := hSpor
    exact phase45_false_of_sporadic hc.hLn hc.hCL e hc.hA1 hc.hA2 hc.hA12 hc.hA12c
  · obtain ⟨e⟩ := hLieD
    rcases hcases with hd | hd | ⟨hchar, hrank⟩
    · exact phase45_false_of_tits hc.hLn hc.hLs hc.hLnab hc.hCL hd e hc.hA1
    · have hch2 : d.1.characteristic = 2 := by
        rw [hd, TauCeti.LieTypeIndex.characteristic_suzuki]
      have htits : d.1 ≠ .tits := by
        rw [hd]
        intro hEq
        cases hEq
      exact phase45_false_of_charTwo hK1a hK1b hc e hch2 htits
    · obtain ⟨q, hq | hq⟩ := hrank
      · have hsmall : SmallWeylIndex45 d.1 := by
          rw [hq]
          norm_num [SmallWeylIndex45]
        exact hK2 X L A₁ A₂ B d hc.hLn hc.hCL ⟨e⟩ hsmall (by omega) (by omega)
          hc.hA1 hc.hA2 hc.hA12 hc.hA12c hc.hB5 hc.hBA1 hc.hBA2 hc.hcomm hc.hlines
      · have hsmall : SmallWeylIndex45 d.1 := by
          rw [hq]
          norm_num [SmallWeylIndex45]
        exact hK2 X L A₁ A₂ B d hc.hLn hc.hCL ⟨e⟩ hsmall (by omega) (by omega)
          hc.hA1 hc.hA2 hc.hA12 hc.hA12c hc.hB5 hc.hBA1 hc.hBA2 hc.hcomm hc.hlines

end StepOne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
