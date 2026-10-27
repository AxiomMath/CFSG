module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16t3_alt_factorial_valuations {n N : ℕ} (hn5 : 5 ≤ n) (hn : n < 12)
    (hcard : N = n.factorial / 2) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ N) ∧ ¬ 7 ^ 2 ∣ N := by
  subst hcard
  have hn11 : n ≤ 11 := by omega
  constructor
  · intro p hp hp5 hd
    have h2dvd : 2 ∣ n.factorial :=
      Nat.dvd_factorial (by norm_num) (by omega)
    have hpdvd : p ∣ n.factorial / 2 :=
      dvd_trans (dvd_pow_self p (by norm_num)) hd
    have hpdvd' : p ∣ n.factorial := by
      rw [← Nat.div_mul_cancel h2dvd]
      exact dvd_mul_of_dvd_left hpdvd 2
    have hpn : p ≤ n := (hp.dvd_factorial).mp hpdvd'
    have hp_cases : p = 5 ∨ p = 7 ∨ p = 11 := by
      have hp11 : p ≤ 11 := by omega
      interval_cases p <;> norm_num at hp
      all_goals omega
    rcases hp_cases with rfl | rfl | rfl <;>
      interval_cases n <;> norm_num [Nat.factorial] at hd
  · interval_cases n <;> norm_num [Nat.factorial]

theorem s16t3_val_card_alt {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    {n : ℕ} (hX : UC22.IsAlt X n) (hn : n < 12) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 3 ∣ Nat.card X) ∧ ¬ 7 ^ 2 ∣ Nat.card X := by
  have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hq hX
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨e⟩ := hX
  have hcard : Nat.card X = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  exact s16t3_alt_factorial_valuations hn5 hn hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
