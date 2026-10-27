module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.SectionRank

theorem nk_leafL2TwentyFive : NKLeafL2TwentyFive := by
  intro X _ _ h
  obtain ⟨-, -, hr⟩ := classical_model_rank (by norm_num : (5 : ℕ) ≠ 2) h
  rcases hr with ⟨-, ⟨-, h1⟩ | ⟨h3, -⟩ | h4⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
  · simpa using h1
  · omega
  · omega
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem nk_leafU3FiveP : NKLeafU3FiveP := by
  intro X _ _ h
  obtain ⟨-, -, hr⟩ := classical_model_rank (by norm_num : (5 : ℕ) ≠ 2) h
  rcases hr with ⟨ht, -⟩ | ⟨-, ⟨-, h1⟩ | h4⟩ | ⟨ht, -⟩ | h4
  · exact absurd ht (by decide)
  · simpa using h1
  · omega
  · exact absurd ht (by decide)
  · omega

theorem nk_leafL2Dvd3 : NKLeafL2Dvd3 := by
  intro p hp hp5 X _ h
  have hp2 : p ≠ 2 := by omega
  have h2 := CFSG.Open.StatedAPI.two_mul_card_of_statedClassicalModel_psl_two_prime hp hp2 h
  have hp3 : ¬ 3 ∣ p := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have hdvd : 3 ∣ p * (p ^ 2 - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 1 ∨ p = 3 * k + 2 := ⟨p / 3, by omega⟩
    rcases hk with rfl | rfl
    · refine ⟨(3 * k + 1) * (3 * k ^ 2 + 2 * k), ?_⟩
      have : (3 * k + 1) ^ 2 - 1 = 3 * (3 * k ^ 2 + 2 * k) := by
        have e : (3 * k + 1) ^ 2 = 3 * (3 * k ^ 2 + 2 * k) + 1 := by ring
        omega
      rw [this]
      ring
    · refine ⟨(3 * k + 2) * (3 * k ^ 2 + 4 * k + 1), ?_⟩
      have : (3 * k + 2) ^ 2 - 1 = 3 * (3 * k ^ 2 + 4 * k + 1) := by
        have e : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
        omega
      rw [this]
      ring
  rw [← h2] at hdvd
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) hdvd)

end CFSG.Quasithin.H13.L829NK
