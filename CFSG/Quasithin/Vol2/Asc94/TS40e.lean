module

public import CFSG.Quasithin.Vol2.Asc94.TS40d

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem hcong_of' (p : ℕ) (key : ∀ c ∈ Nat.divisors 64, c % p = 64 % p → c = 64) :
    ∀ c : ℕ, c ∣ 64 → Nat.ModEq p 64 c → c = 64 := by
  intro c hc hmod
  exact key c (Nat.mem_divisors.2 ⟨hc, by norm_num⟩) hmod.symm

theorem Frame3.sum_Sz' (F : Frame3 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) :
    F.Sz.ncard = 9 + (open Classical in if F.Δ 4 ⊆ F.Sz then 12 else 0) +
      (open Classical in if F.Δ 5 ⊆ F.Sz then 12 else 0) +
      (open Classical in if F.Δ 6 ⊆ F.Sz then 24 else 0) := by
  classical
  have hdich := F.dich
  have h0 := F.Δ0_sub_Sz
  have h1 := F.Δ1_sub_Sz hU1
  have h2 : F.Δ 2 ⊆ F.Sz := by
    intro a ha
    obtain ⟨haU, ha1, haz⟩ := F.Δ2_sub a ha
    have hA : a ∈ ⋃ i, F.Δ i := Set.mem_iUnion.2 ⟨2, ha⟩
    rw [F.Δ_union] at hA
    exact ⟨hA.1, ha1, hU2 a haU ha1⟩
  have h3 := F.not_Δ3_sub_Sz
  have hsum := F.ncard_Sz_eq_sum hdich
  rw [Fin.sum_univ_seven, if_pos h0, if_pos h1, if_pos h2, if_neg h3] at hsum
  have c0 : (F.Δ 0).ncard = 1 := by simpa using F.Δ_card 0
  have c1 : (F.Δ 1).ncard = 6 := by simpa using F.Δ_card 1
  have c2 : (F.Δ 2).ncard = 2 := by simpa using F.Δ_card 2
  have c4 : (F.Δ 4).ncard = 12 := by simpa using F.Δ_card 4
  have c5 : (F.Δ 5).ncard = 12 := by simpa using F.Δ_card 5
  have c6 : (F.Δ 6).ncard = 24 := by simpa using F.Δ_card 6
  rw [c0, c1, c2, c4, c5, c6] at hsum
  rw [hsum]

theorem s40_2_card (F : Frame4 G z) (hU1 : ∀ u ∈ F.U, u ≠ 1 → InZG z u)
    (hU2 : ∀ u ∈ F.U2, u ≠ 1 → InZG z u) : F.Sz.ncard = 21 ∨ F.Sz.ncard = 45 := by
  classical
  have hsum := F.toFrame3.sum_Sz' hU1 hU2
  obtain ⟨j, hj4, hjS, hj12⟩ := F.exists_Δ12 hU1 hU2
  have hj45 : j = 4 ∨ j = 5 := by
    have hfin : ∀ j : Fin 7, 4 ≤ j.val → (F.Δ j).ncard = 12 → j = 4 ∨ j = 5 := by
      intro j hj hc
      rw [F.Δ_card j] at hc
      revert hj hc
      fin_cases j <;> simp
    exact hfin j hj4 hj12
  have hex : F.Δ 4 ⊆ F.Sz ∨ F.Δ 5 ⊆ F.Sz := by
    rcases hj45 with rfl | rfl
    · exact Or.inl hjS
    · exact Or.inr hjS
  have hn : F.Sz.ncard = 21 ∨ F.Sz.ncard = 33 ∨ F.Sz.ncard = 45 ∨ F.Sz.ncard = 57 := by
    by_cases h4 : F.Δ 4 ⊆ F.Sz <;> by_cases h5 : F.Δ 5 ⊆ F.Sz <;>
      by_cases h6 : F.Δ 6 ⊆ F.Sz <;> simp [h4, h5, h6] at hsum <;>
      first | omega | (exfalso; rcases hex with h | h <;> contradiction)
  have hcard := Frame2.card_normalizer_A F.toFrame2
  rcases hn with h | h | h | h
  · exact Or.inl h
  · exfalso
    haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    refine Frame2.not_prime_dvd_card_normalizer F.toFrame2 11 (by norm_num)
      (hcong_of' 11 (by decide)) ?_
    rw [hcard, h]
    exact Dvd.dvd.mul_right (by norm_num : 11 ∣ 33) _
  · exact Or.inr h
  · exfalso
    haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    refine Frame2.not_prime_dvd_card_normalizer F.toFrame2 19 (by norm_num)
      (hcong_of' 19 (by decide)) ?_
    rw [hcard, h]
    exact Dvd.dvd.mul_right (by norm_num : 19 ∣ 57) _

end CFSG.Quasithin.A94
