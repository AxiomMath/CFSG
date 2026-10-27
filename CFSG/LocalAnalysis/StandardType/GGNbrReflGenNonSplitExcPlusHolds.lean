module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem largeEvenLabelAll_reflGenW_excPlus_of_recipe {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1)
    (hE7 : lab.tag = .E7 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusReflGenW p 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K))
    (hE8 : lab.tag = .E8 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusReflGenW p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K))
    (hF4 : lab.tag = .F4 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusReflGenW p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW p (ggNbrExcPlusRank lab.tag) R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hE7 hE8 hF4
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hE7 rfl hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hE8 rfl hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hF4 rfl hpq⟩

theorem ggNbrTableBWeylNonSplitOn_excPlus :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitExcPlusLabel := by
  intro p hp hp2 lab hlab hS _
  obtain ⟨htag, hpn⟩ := hS
  have h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1 := by
    refine ⟨?_, hpn⟩
    rcases htag with ⟨h4, -⟩ | h7 | h8
    · exact Or.inr (Or.inr h4)
    · exact Or.inl h7
    · exact Or.inr (Or.inl h8)
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_excPlus hp hp2 h)
    (largeEvenLabelAll_reflGenW_excPlus_of_recipe h ?_ ?_ ?_)).mono
      fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨_, hl, hw⟩
  · intro _ K _ _ _ hpq
    by_cases h35 : p = 3 ∨ p = 5
    · exact ggTorusReflGenW_E7Plus_threeFive h35 K hpq
    · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
        (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
      exact ggTorusReflGenW_E7Plus_large hp h11 K hpq
  · intro _ K _ _ _ hpq
    by_cases h35 : p = 3 ∨ p = 5
    · exact ggTorusReflGenW_E8Plus_threeFive h35 K hpq
    · have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 hpn
        (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
      exact ggTorusReflGenW_E8Plus_large hp h11 K hpq
  · intro ht K _ _ _ hpq
    have hp3 : p ≠ 3 := by
      rcases htag with ⟨-, h3⟩ | h7 | h8
      · exact h3
      · rw [ht] at h7; cases h7
      · rw [ht] at h8; cases h8
    have h3p : 3 < p := by
      have := hp.two_le
      omega
    exact ggTorusReflGenW_F4Plus_of_four hp h3p hpq (NbrTableBExc.ggTorusReflGenW_F4_all hp hp2)

end CFSG.StandardType

end
