module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import Certificates.Certificate1952

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeNonSplitOn_excPlus :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitExcPlusLabel := by
  intro p hp hp2 lab hlab hS _
  obtain ⟨htag, hpn⟩ := hS
  have h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1 := by
    refine ⟨?_, hpn⟩
    rcases htag with ⟨h4, -⟩ | h7 | h8
    · exact Or.inr (Or.inr h4)
    · exact Or.inl h7
    · exact Or.inr (Or.inl h8)
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_excPlus hp hp2 h)
    (ggWTEx1_largeEvenLabelAll_weylTypeW_excPlus_of_recipe h ?_ ?_ ?_)).mono
      fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨_, hl, hw⟩
  · intro _ K _ _ _ hpq
    by_cases h35 : p = 3 ∨ p = 5
    · exact ggWTEx1_weylTypeW_E7Plus_threeFive h35 K hpq
    · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
        (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
      exact ggWTEx1_weylTypeW_E7Plus_large hp h11 K hpq
  · intro _ K _ _ _ hpq
    by_cases h35 : p = 3 ∨ p = 5
    · exact ggWTEx1_weylTypeW_E8Plus_threeFive h35 K hpq
    · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
        (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
      exact ggWTEx1_weylTypeW_E8Plus_large hp h11 K hpq
  · intro ht K _ _ _ hpq
    have hp3 : p ≠ 3 := by
      rcases htag with ⟨-, h3⟩ | h7 | h8
      · exact h3
      · rw [ht] at h7; cases h7
      · rw [ht] at h8; cases h8
    have h3p : 3 < p := by have := hp.two_le; omega
    exact ggWTEx1_weylTypeW_F4Plus_of_four (K := K) hp h3p hpq

end CFSG.StandardType

end
