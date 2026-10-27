module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.PartOne.S11c.ETypeCover
public import CFSG.RankThree.PartOne.S11c.TwistedE6FieldTwoCover
public import CFSG.RankThree.Chevalley.SteinbergBTEvenEModelFieldTwo
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6FieldThreeCover

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.Chevalley CFSG.Assembly.LowTwoRank

theorem actualCoverETypeRankThreeOnlyE6FieldTwo : ActualCoverETypeRankThreeOnlyE6FieldTwo := by
  intro X _ _ he Y ℓ f hℓ hf τ hτ hmod
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have hf1 : f = 1 := actual_central_cover_even_E_model_field_two he Y hf hτ hmod
    subst hf1
    refine ⟨?_, rfl, rfl⟩
    rcases hτ with rfl | rfl | rfl | rfl
    · rfl
    · exfalso
      obtain ⟨-, -, -, -, -, -, -, h4⟩ :=
        E6_E7_model_actual_central_cover_odd_rank_four Y (Or.inr rfl) (Or.inl rfl) hmod
      omega
    · exfalso
      obtain ⟨-, -, h4⟩ := E8_small_field_actual_central_cover_three_rank_four Y (Or.inl rfl) hmod
      omega
    · exfalso
      obtain ⟨-, -, h4⟩ := twisted_E6_field_two_actual_central_cover_local_three_rank_four Y hmod
      omega
  · exfalso
    have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4 := by
      rcases hτ with h | h | h | h <;> simp [h]
    have hne : τ ≠ .trialityD4 := by
      rcases hτ with rfl | rfl | rfl | rfl <;> decide
    have hq : ℓ ^ f = 3 :=
      (actual_central_cover_higher_exceptional_small_field_restrictions he Y hτ' hmod).1 hℓ2 hne
    have hℓ3 : ℓ = 3 := by
      have hdvd : ℓ ∣ 3 := hq ▸ dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hdvd
    subst hℓ3
    have hf1 : f = 1 := by
      have h3 : 3 ^ f = 3 ^ 1 := by rw [hq, pow_one]
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    subst hf1
    rcases hτ with rfl | rfl | rfl | rfl
    · obtain ⟨-, -, -, -, -, -, -, h4⟩ :=
        E6_E7_model_actual_central_cover_odd_rank_four Y (Or.inl rfl) (Or.inr hℓ2) hmod
      omega
    · obtain ⟨-, -, -, -, -, -, -, h4⟩ :=
        E6_E7_model_actual_central_cover_odd_rank_four Y (Or.inr rfl) (Or.inr hℓ2) hmod
      omega
    · obtain ⟨-, -, h4⟩ := E8_small_field_actual_central_cover_three_rank_four Y (Or.inr rfl) hmod
      omega
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hne3⟩ :=
        twisted_E6_field_three_actual_central_cover_local_three_rank_four Y hmod
      exact hne3 he

end CFSG.RankThree.PartOne
