module

public import CFSG.RankThree.PartOne.KE.E8FiveArith

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice

theorem e8T12_odd (q : ℕ) : Odd (q ^ 4 - q ^ 2 + 1) := by
  have h : q ^ 4 - q ^ 2 = q ^ 2 * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_add]
  rw [h]
  exact (Nat.even_mul_pred_self (q ^ 2)).add_one

theorem e8T12_ordProj {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) =
      ordProj[p] ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num) hq2) (by norm_num)
  have hn₀ : q ^ 4 - q ^ 2 + 1 ≠ 0 := by omega
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨hg, -, hR⟩ := CTE6.e6Twelve_factors hp hord
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hn₀Z : (((q ^ 4 - q ^ 2 + 1 : ℕ)) : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
    push_cast [Nat.cast_sub h24]
    ring
  have hR₁ : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 2 + 1) *
      ((q : ℤ) ^ 2 + (q : ℤ) + 1) := fun h =>
    (hpz.dvd_or_dvd h).elim hR hg
  have hq12 : ((q : ZMod p)) ^ 12 = 1 := by
    have := pow_orderOf_eq_one ((q : ℕ) : ZMod p)
    rwa [hord] at this
  have hR₂ : ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 2 + 1) *
      ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 12 + 1) := by
    intro h
    rcases hpz.dvd_or_dvd h with h1 | h1
    · exact hR₁ h1
    · have h2 : (((q : ℤ) ^ 12 + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
      push_cast at h2
      rw [hq12] at h2
      have h3 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h2
      have : Fact p.Prime := ⟨hp⟩
      exact (CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega) : ((2 : ℕ) : ZMod p) ≠ 0) h3
  have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 12 → d ≠ 24 → ¬ 12 ∣ d := by
    decide
  have key := ordProj_card_adjointGroup_E8_two (K := K) (p := p) (m := 12) (d₁ := 12) (d₂ := 24)
    (n₀ := q ^ 4 - q ^ 2 + 1)
    (R₁ := ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1))
    (R₂ := ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1) *
      ((q : ℤ) ^ 12 + 1)) hp hp3 hpq hord (by decide) (by decide) (by decide) hrest hn₀
    (by rw [hcast, hn₀Z]; ring) hR₁ (by rw [hcast, hn₀Z]; ring) hR₂
  rw [key, pow_two (q ^ 4 - q ^ 2 + 1), Nat.ordProj_mul p hn₀ hn₀]

end CFSG.RankThree.PartOne.KE
