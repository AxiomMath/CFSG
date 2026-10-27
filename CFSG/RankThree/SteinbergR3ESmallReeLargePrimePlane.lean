module

public import CFSG.RankThree.SteinbergR3ESmallReeAutPrimes

public noncomputable section

namespace CFSG.RankThree.ReeTitsAut

open CFSG.Blueprint CFSG.LieType.Ree

theorem not_sq_dvd_large_part {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ 7 * 13 * 19 * 37 := by
  intro h
  have hpd : p ∣ 7 * 13 * 19 * 37 := (dvd_pow_self p two_ne_zero).trans h
  have hp7 : (7 : ℕ).Prime := by norm_num
  have hp13 : (13 : ℕ).Prime := by norm_num
  have hp19 : (19 : ℕ).Prime := by norm_num
  have hp37 : (37 : ℕ).Prime := by norm_num
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · rw [(Nat.prime_dvd_prime_iff_eq hp hp7).1 h3] at h
        norm_num at h
      · rw [(Nat.prime_dvd_prime_iff_eq hp hp13).1 h3] at h
        norm_num at h
    · rw [(Nat.prime_dvd_prime_iff_eq hp hp19).1 h2] at h
      norm_num at h
  · rw [(Nat.prime_dvd_prime_iff_eq hp hp37).1 h1] at h
    norm_num at h

theorem small_Ree_actual_central_cover_no_large_prime_automorphism_plane {H : Type} [Group H]
    [Finite H] (hH : CFSG.twoLocalOddRank H ≤ 3) (X : Subgroup H) (ℓ f : ℕ)
    (h : ReeTitsModel (X ⧸ Subgroup.center X) .twistedG2 ℓ f) :
    ℓ = 3 ∧ f = 3 ∧ ∀ p : ℕ, p.Prime → 3 < p →
      ¬ p ^ 2 ∣ Nat.card (MulAut (X ⧸ Subgroup.center X)) ∧
      ∀ E : Subgroup (MulAut (X ⧸ Subgroup.center X)), CFSG.IsElementaryAbelian p E →
        Nat.card E ≠ p ^ 2 := by
  obtain ⟨hℓ, hf, k, hk⟩ := small_Ree_small_rank_core X ℓ f h hH
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  refine ⟨hℓ, hf, fun p hp hp3 => ?_⟩
  have hsq : ¬ p ^ 2 ∣ Nat.card (MulAut (X ⧸ Subgroup.center X)) := fun hdvd => by
    have h1 := hdvd.trans hk
    have hcop3 : Nat.Coprime (p ^ 2) (3 ^ k) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
    have h2 := hcop3.dvd_of_dvd_mul_left h1
    have hN : (3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1) =
        (2 ^ 3 * 3 ^ 9) * (7 * 13 * 19 * 37) := by
      norm_num
    rw [hN] at h2
    have hcop : Nat.Coprime (p ^ 2) (2 ^ 3 * 3 ^ 9) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
    exact not_sq_dvd_large_part hp (hcop.dvd_of_dvd_mul_left h2)
  refine ⟨hsq, fun E _ hE => hsq ?_⟩
  rw [← hE]
  exact Subgroup.card_subgroup_dvd_card E

end CFSG.RankThree.ReeTitsAut
