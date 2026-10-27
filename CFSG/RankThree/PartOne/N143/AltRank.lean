module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartOne.SecRank.CentralizerRank
import CFSG.RankThree.PartOne.SecRank.AltRank
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem localRank_le_factorization {S : Type} [Group S] [Finite S] {r : ℕ} (hr : r.Prime) :
    localRank r S ≤ (Nat.card S).factorization r := by
  unfold localRank CFSG.Open.twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨H, -, rfl⟩
  have h := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card r hr H
  have h2 : r ^ CFSG.Assembly.pRank r H ∣ Nat.card S := h.trans (Subgroup.card_subgroup_dvd_card H)
  exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h2

theorem not_pow_four_dvd_factorial_eleven {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    ¬ r ^ 4 ∣ Nat.factorial 11 := by
  intro h
  have hle : r ^ 4 ≤ Nat.factorial 11 := Nat.le_of_dvd (Nat.factorial_pos 11) h
  have hr80 : r < 80 := by
    by_contra h80
    have : 80 ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h11 : Nat.factorial 11 = 39916800 := by decide
    omega
  have key : ∀ r < 80, r.Prime → 5 ≤ r → ¬ r ^ 4 ∣ Nat.factorial 11 := by decide
  exact key r hr80 hr hr5 h

theorem evenRank_alternating_le_three {n : ℕ} (hn : n ≤ 11) :
    evenRank (alternatingGroup (Fin n)) ≤ 3 := by
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    have := CFSG.RankThree.PartOne.SecRank.localRank_three_le_of_centralizer (H := alternatingGroup (Fin n))
      2 (fun t ht h27 =>
        CFSG.RankThree.PartOne.SecRank.not_dvd_card_centralizer_alternating (n := n) (by omega) t ht
          (by simpa using h27))
    omega
  · have hr5 : 5 ≤ r := by
      have := hr.two_le
      rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with h | h | h | h
      · exact absurd h hr2
      · exact absurd h hr3
      · exact absurd (h ▸ hr) (by norm_num)
      · exact h
    refine (localRank_le_factorization hr).trans ?_
    by_contra hlt
    push Not at hlt
    have hcard : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 11 := by
      refine (Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))).trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      exact Nat.factorial_dvd_factorial hn
    have h4 : r ^ 4 ∣ Nat.card (alternatingGroup (Fin n)) :=
      (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 (by omega)
    exact not_pow_four_dvd_factorial_eleven hr hr5 (h4.trans hcard)

end CFSG.RankThree.PartOne.N143
