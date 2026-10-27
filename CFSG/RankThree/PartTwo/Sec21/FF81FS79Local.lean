module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fr6

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace J6

theorem card_Nor_T1 : Nat.card (Nor T1) = 48 := by
  rw [card_of_finset NT1 (Nor T1) (fun σ => ?_), NT1_card]
  simp only [NT1, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hσ s hs
    exact (Subgroup.mem_normalizer_iff.mp hσ s).mp hs
  · intro h
    exact Subgroup.mem_normalizer_fintype fun s hs => h s hs

theorem card_Nor_V1 : Nat.card (Nor V1) = 48 := by
  rw [card_of_finset NV1 (Nor V1) (fun σ => ?_), NV1_card]
  simp only [NV1, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hσ s hs
    exact (Subgroup.mem_normalizer_iff.mp hσ s).mp hs
  · intro h
    exact Subgroup.mem_normalizer_fintype fun s hs => h s hs

theorem R_norm_T1 : ∀ r ∈ R, ∀ s ∈ T1, r * s * r⁻¹ ∈ T1 := by
  intro r hr s hs
  have h1 : r ∈ NT1 := R_sub_NT1 hr
  simp only [NT1, Finset.mem_filter, Finset.mem_univ, true_and] at h1
  exact h1 s hs

theorem R_norm_V1 : ∀ r ∈ R, ∀ s ∈ V1, r * s * r⁻¹ ∈ V1 := by
  intro r hr s hs
  have h1 : r ∈ NV1 := R_sub_NV1 hr
  simp only [NV1, Finset.mem_filter, Finset.mem_univ, true_and] at h1
  exact h1 s hs

theorem R_conj_T1 : ∀ r ∈ R, r * r = 1 → ∃ γ : S6, γ * r * γ⁻¹ ∈ T1 := by
  intro r hr hr2
  rcases R_inv_mem r hr hr2 with h1 | h1
  · exact ⟨1, by rw [inv_one, one_mul, mul_one]; exact h1⟩
  · obtain ⟨γ, -, hγ⟩ := V1_conj_T1 r h1
    exact ⟨γ, hγ⟩

theorem R_conj_V1 : ∀ r ∈ R, r * r = 1 → ∃ γ : S6, γ * r * γ⁻¹ ∈ V1 := by
  intro r hr hr2
  rcases R_inv_mem r hr hr2 with h1 | h1
  · obtain ⟨γ, -, hγ⟩ := T1_conj_V1 r h1
    exact ⟨γ, hγ⟩
  · exact ⟨1, by rw [inv_one, one_mul, mul_one]; exact h1⟩

end J6

variable {H : Type} [Group H] [Finite H]

end CFSG.RankThree.PartTwo.Sec21.FF81
