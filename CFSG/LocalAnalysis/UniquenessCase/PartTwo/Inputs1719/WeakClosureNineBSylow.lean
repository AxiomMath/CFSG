module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBBlocks

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup

theorem TB_le_of {i : Fin 4} {P : Subgroup P16} (hTD : TD ≤ P) (hb : ∀ g ∈ bGens i, g ∈ P) :
    TB i ≤ P := by
  rw [TB, closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hTD (subset_closure hx)
  · exact hb x hx

theorem eq_TB2_of {P : Subgroup P16} (h3 : P ≤ TB 3) (hTD : TD ≤ P) (hsig : sig ∈ P)
    (hcard : Nat.card P = 256) : P = TB 2 := by
  have hidx : (P.subgroupOf (TB 3)).index = 2 := by
    have h1 := relIndex_mul_card (H := P) (K := TB 3)
    rw [inf_eq_left.2 h3, hcard, card_TB3] at h1
    change P.relIndex (TB 3) = 2
    omega
  have hnorm := normal_of_index_eq_two hidx
  have hd1 : d1 ∈ TB 3 := mem_TB (by simp [bGens])
  have hsig3 : sig ∈ TB 3 := mem_TB (by simp [bGens])
  have hc : d1 * sig * d1⁻¹ ∈ P := hnorm.conj_mem ⟨sig, hsig3⟩ hsig ⟨d1, hd1⟩
  have hd12 : d1 * d2 ∈ P := by
    rw [← d1_conj_sig]
    exact mul_mem hc (inv_mem hsig)
  have hle : TB 2 ≤ P := TB_le_of hTD fun g hg => by
    simp only [bGens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hsig
    · exact hd12
  exact (eq_of_le_of_card_ge hle (by rw [hcard, card_TB2])).symm

theorem eq_TB_of {P : Subgroup P16} (h3 : P ≤ TB 3) (hTD : TD ≤ P)
    (hsw : sig ∈ P ∨ d1 * sig ∈ P) : ∃ i, P = TB i := by
  have hdvd1 : Nat.card P ∣ 2 ^ 9 := by
    rw [show (2 : ℕ) ^ 9 = 512 by norm_num, ← card_TB3]
    exact card_dvd_of_le h3
  have hdvd2 : 2 ^ 6 ∣ Nat.card P := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← card_TD]
    exact card_dvd_of_le hTD
  have hne : Nat.card P ≠ 64 := by
    intro h
    have hPD : TD = P := eq_of_le_of_card_ge hTD (by rw [h, card_TD])
    rcases hsw with h' | h'
    · exact sig_not_mem_TD (hPD ▸ h')
    · exact d1sig_not_mem_TD (hPD ▸ h')
  have hTB0 : sig ∈ P → TB 0 ≤ P := fun h => TB_le_of hTD fun g hg => by
    simp only [bGens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]
    exact h
  have hTB1 : d1 * sig ∈ P → TB 1 ≤ P := fun h => TB_le_of hTD fun g hg => by
    simp only [bGens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]
    exact h
  obtain ⟨k, hk, hkP⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hk6 : 6 ≤ k := by
    rw [hkP] at hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd2
  interval_cases k
  · exact absurd (by rw [hkP]; norm_num) hne
  · rcases hsw with h | h
    · exact ⟨0, (eq_of_le_of_card_ge (hTB0 h) (by rw [hkP, card_TB0]; norm_num)).symm⟩
    · have h1 := card_le_of_le (hTB1 h)
      rw [card_TB1, hkP] at h1
      norm_num at h1
  · rcases hsw with h | h
    · exact ⟨2, eq_TB2_of h3 hTD h (by rw [hkP]; norm_num)⟩
    · exact ⟨1, (eq_of_le_of_card_ge (hTB1 h) (by rw [hkP, card_TB1]; norm_num)).symm⟩
  · exact ⟨3, eq_of_le_of_card_ge h3 (by rw [hkP, card_TB3]; norm_num)⟩

end CFSG.LocalAnalysis.WeakClosure81.NGM
