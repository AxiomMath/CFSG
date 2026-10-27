module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OL2Arith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.Quasithin.H13.NQCore.L2Odd

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem card_perm_four' : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem three_dvd_sq_sub_one {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    3 ∣ (p ^ m) ^ 2 - 1 := by
  have h3 : ¬ 3 ∣ p := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h) (by omega)
  have h3m : ¬ 3 ∣ p ^ m := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have h1 : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
  have h2 : (p ^ m) ^ 2 % 3 = 1 := by
    have : p ^ m % 3 = 1 ∨ p ^ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [pow_two, Nat.mul_mod, h]
  omega

theorem false_of_dickson {p k m : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hm : ¬ 2 ∣ m)
    (hk : 2 ^ k * m = p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2))
    (H : Subgroup PSL(2, GaloisField p 2)) (hH : Nat.card H = p ^ 2 * 2 ^ k) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨c, hc⟩ := exists_sq_eq (hp.out.odd_of_ne_two hp2)
  rw [sq_sq_sub_one_div_two hc] at hk
  obtain ⟨hpc, hpc1⟩ := not_dvd_of_sq hp.out hp2 hc
  have hodd : ¬ p ∣ 2 := fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)
  have hgcd : Nat.gcd 2 (p ^ 2 - 1) = 2 := by
    have : p ^ 2 - 1 = 2 * c := by omega
    rw [this]
    exact Nat.gcd_eq_left (dvd_mul_right 2 c)
  have hpH : p ∣ Nat.card H := hH ▸ Dvd.dvd.mul_right (dvd_pow_self p two_ne_zero) _
  have h3 : ¬ 3 ∣ Nat.card H := by
    rw [hH]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).1
        (Nat.prime_three.dvd_of_dvd_pow h)) (by omega)
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
  have hpm : ∀ n : ℕ, 3 ∣ p ^ n * (((p ^ n) ^ 2 - 1) / 2) := by
    intro n
    have hd := three_dvd_sq_sub_one hp.out hp5 (m := n)
    have h2 : 2 * (((p ^ n) ^ 2 - 1) / 2) = (p ^ n) ^ 2 - 1 := by
      obtain ⟨c', hc'⟩ := exists_sq_eq ((hp.out.odd_of_ne_two hp2).pow (n := n))
      rw [hc']
      omega
    refine Dvd.dvd.mul_left ?_ _
    rw [← h2] at hd
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hd)
  have hdiv : ∀ n : ℕ, (n ∣ (p ^ 2 + 1) / Nat.gcd 2 (p ^ 2 - 1) ∨
      n ∣ (p ^ 2 - 1) / Nat.gcd 2 (p ^ 2 - 1)) → ¬ p ∣ n := by
    intro n hn hpn
    rw [hgcd, show (p ^ 2 + 1) / 2 = c + 1 by omega, show (p ^ 2 - 1) / 2 = c by omega] at hn
    rcases hn with hn | hn
    · exact hpc1 (hpn.trans hn)
    · exact hpc (hpn.trans hn)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      apply hm
      rw [pow_zero, one_mul] at hk
      rw [hk]
      exact ⟨p ^ 2 * (c * (c + 1)), by ring⟩
    · exact h
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  rcases F6.dicksonPSL2_holds p 2 (by norm_num) H with
      ⟨-, n, -, hn⟩ | ⟨-, hdvd⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨n, t, P, hPn, -, hPc, -, hQt, -, htq⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have h2 : 2 ∣ p ^ n := by
      rw [← hn, hH]
      exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  · exact hdiv _ hdvd hpH
  · have hc' := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hc'
    rw [hc'] at hpH
    exact hdiv z hz (((Nat.Prime.dvd_mul hp.out).1 hpH).resolve_left hodd)
  · exact h3 (by rw [Nat.card_congr e.toEquiv, card_alternating_four']; norm_num)
  · exact h3 (by rw [Nat.card_congr e.toEquiv, card_perm_four']; norm_num)
  · exact h3 (by rw [Nat.card_congr e.toEquiv, card_alternating_five']; norm_num)
  · have hHt : Nat.card H = t * p ^ n := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    have h2t : 2 ^ k ∣ t * p ^ n := by
      rw [← hHt, hH]
      exact dvd_mul_left _ _
    have h2t' : 2 ^ k ∣ t := (Nat.Coprime.pow_right n hcop).dvd_of_dvd_mul_right h2t
    rw [hgcd, show (p ^ 2 - 1) / 2 = c by omega] at htq
    exact not_two_pow_dvd hm hk (h2t'.trans htq)
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hn) (by norm_num)
    have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn0
    have hcard := Nat.card_congr e.toEquiv
    rw [CFSG.SectionRank.OddCover.card_psl_two hp.out hp2 hK] at hcard
    exact h3 (hcard ▸ hpm n)
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hn) (by norm_num)
    have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn0
    have hcard := Nat.card_congr e.toEquiv
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK] at hcard
    exact h3 (hcard ▸ Dvd.dvd.mul_left (three_dvd_sq_sub_one hp.out hp5) _)

end CFSG.Quasithin.H13.NQCore.L2Odd
