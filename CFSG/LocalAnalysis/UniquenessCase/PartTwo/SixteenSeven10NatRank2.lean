module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section SumOfTwo

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c1610_le_rk_sumOfNat_two {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U : Subgroup W} {r : ℕ}
    (hN : ∀ I : Subgroup W, N H I ⊥ → r ≤ rk ↥I) (h : SumOfNat N H U ⊥ 2) : 2 * r ≤ rk ↥U := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    have h0 := hind 0
    have h1 : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_sup_of_le_right (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
    exact le_bot_iff.mp (le_trans (inf_le_inf_left _ h1) h0)
  have hU : I 0 ⊔ I 1 = U := by
    rw [← hsup, bot_sup_eq]
    apply le_antisymm
    · exact sup_le (le_iSup I 0) (le_iSup I 1)
    · exact iSup_le fun i => by fin_cases i <;> simp
  have h := rk_sup_add_rk_inf (I 0) (I 1)
  have h0 := hN _ (hnat 0)
  have h1 := hN _ (hnat 1)
  rw [h01, hU, rk_bot] at h
  omega

end SumOfTwo

section Alternating

open CFSG.Quasithin.G6

variable {V : Type} [CommGroup V]

private theorem allOnes_sq_two (n : ℕ) : allOnes n ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [allOnes, toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply]
  decide

private theorem card_altKer_dvd_two (n : ℕ) :
    Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n) ∣ 2 :=
  calc Nat.card ↥(Subgroup.zpowers (allOnes n) ⊓ coreMod n)
      ∣ Nat.card ↥(Subgroup.zpowers (allOnes n)) := Subgroup.card_dvd_of_le inf_le_left
    _ = orderOf (allOnes n) := Nat.card_zpowers _
    _ ∣ 2 := orderOf_dvd_of_pow_eq_one (allOnes_sq_two n)

theorem s16c1610_le_rk_alternatingNatural {H : Subgroup (MulAut V)} {U : Subgroup V} {n : ℕ}
    (hn : 2 ≤ n) (h : AlternatingNatural H U ⊥ n) : n - 2 ≤ rk ↥U := by
  have h1 := s16c1610_card_alternatingNatural_mul (by omega) h
  rcases (Nat.dvd_prime Nat.prime_two).1 (card_altKer_dvd_two n) with h2 | h2
  · rw [h2, mul_one] at h1
    rw [s16c1610_rk_of_card_two_pow h1]
    omega
  · rw [h2] at h1
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ] at h1
    have h3 : Nat.card U = 2 ^ k := Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    rw [s16c1610_rk_of_card_two_pow h3]
    omega

theorem s16c1610_rk_alternatingNatural_odd {H : Subgroup (MulAut V)} {U : Subgroup V} {n : ℕ}
    (hn : Odd n) (h : AlternatingNatural H U ⊥ n) : rk ↥U = n - 1 :=
  s16c1610_rk_of_card_two_pow (s16c1610_card_alternatingNatural_odd hn h)

end Alternating

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
