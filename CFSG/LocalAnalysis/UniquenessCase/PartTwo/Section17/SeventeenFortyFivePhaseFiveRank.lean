module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseFiveRankClassical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseFiveRankExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open TauCeti.LieTypeIndex (characteristic_A characteristic_B characteristic_C characteristic_D
  characteristic_E6 characteristic_E7 characteristic_E8 characteristic_F4 characteristic_G2
  characteristic_reeF4 characteristic_suzuki characteristic_tits characteristic_trialityD4
  characteristic_twistedA characteristic_twistedD characteristic_twistedE6)

theorem k45FiveRankTwo_holds :
    K45FiveRankTwo := by
  intro K _ _ d ⟨e⟩ h2 h5 hd
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r q =>
    rcases hd with hd | ⟨h31, -, hrank⟩
    · simp [BigNonLinIndex45] at hd
    · exact two_le_pRank_five_A r q hv e (characteristic_A r q ▸ h31)
        fun h => hrank ⟨q, Or.inl (by subst h; rfl)⟩
  | twistedA r q =>
    rcases hd with hd | ⟨h31, -, hrank⟩
    · simp [BigNonLinIndex45] at hd
    · exact two_le_pRank_five_twistedA r q hv e (characteristic_twistedA r q ▸ h31)
        fun h => hrank ⟨q, Or.inr (by subst h; rfl)⟩
  | B r q =>
    refine two_le_pRank_five_B r q hv e (characteristic_B r q ▸ h5) ?_
    rcases hd with hd | ⟨h31, -, -⟩
    · exact Or.inl hd
    · exact Or.inr (characteristic_B r q ▸ h31)
  | C r q =>
    refine two_le_pRank_five_C r q hv e (characteristic_C r q ▸ h5) ?_
    rcases hd with hd | ⟨h31, -, -⟩
    · exact Or.inl hd
    · exact Or.inr (characteristic_C r q ▸ h31)
  | D r q =>
    refine two_le_pRank_five_D r q hv e (characteristic_D r q ▸ h5) ?_
    rcases hd with hd | ⟨h31, -, -⟩
    · exact Or.inl hd
    · exact Or.inr (characteristic_D r q ▸ h31)
  | twistedD r q =>
    refine two_le_pRank_five_twistedD r q hv e (characteristic_twistedD r q ▸ h5) ?_
    rcases hd with hd | ⟨h31, -, -⟩
    · exact Or.inl hd
    · exact Or.inr (characteristic_twistedD r q ▸ h31)
  | E6 q =>
    exact two_le_pRank_five_E6 q hv e (characteristic_E6 q ▸ h2)
      (characteristic_E6 q ▸ h5)
  | E7 q =>
    exact two_le_pRank_five_E7 q hv e (characteristic_E7 q ▸ h2)
      (characteristic_E7 q ▸ h5)
  | E8 q =>
    exact two_le_pRank_five_E8 q hv e (characteristic_E8 q ▸ h2)
      (characteristic_E8 q ▸ h5)
  | twistedE6 q =>
    exact two_le_pRank_five_twistedE6 q hv e (characteristic_twistedE6 q ▸ h2)
      (characteristic_twistedE6 q ▸ h5)
  | G2 q =>
    rcases hd with hd | ⟨h31, -, -⟩
    · simp [BigNonLinIndex45] at hd
    · exact two_le_pRank_five_G2 q hv e (characteristic_G2 q ▸ h31)
  | F4 q =>
    rcases hd with hd | ⟨h31, -, -⟩
    · simp [BigNonLinIndex45] at hd
    · exact two_le_pRank_five_F4 q hv e (characteristic_F4 q ▸ h31)
  | trialityD4 q =>
    rcases hd with hd | ⟨h31, -, -⟩
    · simp [BigNonLinIndex45] at hd
    · exact two_le_pRank_five_trialityD4 q hv e (characteristic_trialityD4 q ▸ h31)
  | suzuki m => exact absurd (characteristic_suzuki m) h2
  | reeG2 m =>
    rcases hd with hd | ⟨-, hs, -⟩
    · simp [BigNonLinIndex45] at hd
    · simp [SmallWeylIndex45] at hs
  | reeF4 m => exact absurd (characteristic_reeF4 m) h2
  | tits => exact absurd characteristic_tits h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
