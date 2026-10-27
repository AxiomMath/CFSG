module

public import CFSG.RankThree.PartOne.KE.E8FiveArith

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Lattice

theorem e8T8_ordProj {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 8) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) =
      ordProj[p] ((Nat.card K ^ 4 + 1) ^ 2) := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  set q : ℕ := Nat.card K with hqdef
  have hn₀ : q ^ 4 + 1 ≠ 0 := by positivity
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcast : ∀ d : ℕ, ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := fun d => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hn₀Z : (((q ^ 4 + 1 : ℕ)) : ℤ) = (q : ℤ) ^ 4 + 1 := by
    push_cast
    ring
  have hne4 : (q : ZMod p) ^ 4 ≠ 1 := CTE6.pow_ne_one_of_orderOf hord (by norm_num)
  have hq8 : (q : ZMod p) ^ 8 = 1 := by
    have := pow_orderOf_eq_one ((q : ℕ) : ZMod p)
    rwa [hord] at this
  have hR₁ : ¬ (p : ℤ) ∣ (q : ℤ) ^ 4 - 1 :=
    CTE6.not_dvd_of_pow_ne_one hne4 (P := (q : ℤ) ^ 4 - 1) (Q := 1) (by ring)
  have hR₂ : ¬ (p : ℤ) ∣ ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 16 + (q : ℤ) ^ 8 + 1) := by
    intro h
    rcases hpz.dvd_or_dvd h with h1 | h1
    · exact hR₁ h1
    · have h2 : (((q : ℤ) ^ 16 + (q : ℤ) ^ 8 + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
      push_cast at h2
      have h16 : (q : ZMod p) ^ 16 = 1 := by
        calc (q : ZMod p) ^ 16 = ((q : ZMod p) ^ 8) ^ 2 := by ring
          _ = 1 := by rw [hq8]; ring
      rw [h16, hq8] at h2
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h2
      have : Fact p.Prime := ⟨hp⟩
      exact (CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega) : ((3 : ℕ) : ZMod p) ≠ 0) h3
  have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 8 → d ≠ 24 → ¬ 8 ∣ d := by
    decide
  have key := ordProj_card_adjointGroup_E8_two (K := K) (p := p) (m := 8) (d₁ := 8) (d₂ := 24)
    (n₀ := q ^ 4 + 1) (R₁ := (q : ℤ) ^ 4 - 1)
    (R₂ := ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 16 + (q : ℤ) ^ 8 + 1)) hp hp3 hpq hord (by decide)
    (by decide) (by decide) hrest hn₀ (by rw [hcast, hn₀Z]; ring) hR₁
    (by rw [hcast, hn₀Z]; ring) hR₂
  rw [key, pow_two (q ^ 4 + 1), Nat.ordProj_mul p hn₀ hn₀]

end CFSG.RankThree.PartOne.KE
