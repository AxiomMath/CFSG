module

public import CFSG.RankThree.PartOne.N143.HeisenbergThree
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSU)

theorem card_outer_projSU_four_eq {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (Outer (projSU 4 p f)) = 2 * f * Nat.gcd 4 (p ^ f + 1) := by
  have hU := unitaryFieldData_galoisField p f hf
  have e : projSU 4 p f ≃* unitaryPSU hU 4 :=
    (projSUEquivStatedProj 4 p f).trans (unitaryPSUEquiv hU (n := 4) (by norm_num)).symm
  have hout := (unitary_full_diagonal_outer_order (n := 4) hU (by norm_num) (by norm_num)).2.2.2.2.1
  rw [Nat.card_congr (equivalence e).toEquiv, hout]

theorem not_three_dvd_card_outer_projSU_four_two {m : ℕ} (hm : 1 ≤ m) (h3 : ¬ 3 ∣ m) :
    ¬ 3 ∣ Nat.card (Outer (projSU 4 2 m)) := by
  rw [card_outer_projSU_four_eq hm]
  have hodd : Nat.gcd 4 (2 ^ m + 1) = 1 := by
    have h2 : (2 : ℕ) ^ m % 2 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      simp [pow_add, Nat.mul_mod]
    have hcop : Nat.Coprime 2 (2 ^ m + 1) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    have : Nat.Coprime (2 ^ 2) (2 ^ m + 1) := Nat.Coprime.pow_left 2 hcop
    simpa using this
  rw [hodd]
  intro h
  have h' : 3 ∣ 2 * m * 1 := h
  rw [mul_one] at h'
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h2 | h2
  · omega
  · exact h3 h2

theorem not_three_dvd_card_outer_projSU_four_prime {p : ℕ} [Fact p.Prime] :
    ¬ 3 ∣ Nat.card (Outer (projSU 4 p 1)) := by
  rw [card_outer_projSU_four_eq le_rfl, pow_one]
  have hg : Nat.gcd 4 (p + 1) ∣ 4 := Nat.gcd_dvd_left 4 (p + 1)
  intro h
  have h1 : 3 ∣ 2 * 1 * Nat.gcd 4 (p + 1) := h
  have h2 : 3 ∣ Nat.gcd 4 (p + 1) := by
    rw [mul_one] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h3 | h3
    · omega
    · exact h3
  have h3 : 3 ∣ 4 := h2.trans hg
  omega

theorem outerRow_projSU_four_prime {p : ℕ} [Fact p.Prime] : OuterRow (projSU 4 p 1) :=
  outerRow_of_not_three_dvd_outer not_three_dvd_card_outer_projSU_four_prime

end CFSG.RankThree.PartTwo.Sec4.RonanK432
