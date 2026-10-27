module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRest
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCSylowHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCOutHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSpor KStrongEmbedded72)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72 R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_14 R6_38)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

theorem list863_of_lieModel_g2_of_choiceX
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (hsig4 : SigmaIsRankFour D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    {p f : ℕ} (hK : LieModel (Bar2 L) .G2 0 p f) : List863 (Bar2 L) := by
  obtain ⟨hp, hf, -, h3q⟩ := hK.admissible
  have hp3 : p ≠ 3 := p_ne_three_of_cex856_g2 hX.cex hK
  by_cases h5 : p ^ f = 5
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h5
    exact Or.inr (Or.inr (Or.inl hK))
  by_cases h7 : p ^ f = 7
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
    exact Or.inr (Or.inr (Or.inr (Or.inl hK)))
  by_cases h17 : p ^ f = 17
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 17)).mp h17
    exact Or.inr (Or.inr (Or.inr (Or.inr hK)))
  exact (false_of_lie_families_of_choiceX g2NonsplitSylowInput_holds trialityTorusSylowInput_holds
    lieOutCyclicInput_holds hSg hsig4 h614 h638 h858 h72 h76 hKF7 hX hLX
    (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hK)
    (Or.inl ⟨p, f, hK, hp, hp3, hf, h3q, h5, h7, h17⟩)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
