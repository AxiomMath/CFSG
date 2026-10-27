module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KRepFix
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Field

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91cf3_two_sub_eq_three {R : Type*} [Ring R] {x : R} (h : 1 + x + x ^ 2 = 0) :
    2 - x - x ^ 2 = 3 := by
  have h1 : (1 : R) + (x + x ^ 2) = 0 := by rwa [← add_assoc]
  rw [sub_sub, eq_neg_of_add_eq_zero_right h1, sub_neg_eq_add, two_add_one_eq_three]

private theorem k91cf3_not_dvd {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) : ¬ q ∣ 32400 := by
  intro hd
  have hle : ∀ {m n : ℕ}, 0 < m → q ∣ m ^ n → q ≤ m := fun hm hmn =>
    Nat.le_of_dvd hm (hq.dvd_of_dvd_pow hmn)
  rcases hq.dvd_mul.1 (show q ∣ 2 ^ 4 * 3 ^ 4 * 5 ^ 2 from hd) with h | h
  · rcases hq.dvd_mul.1 h with h | h
    · exact absurd (hle (by omega) h) (by omega)
    · exact absurd (hle (by omega) h) (by omega)
  · exact absurd (hle (by omega) h) (by omega)

private theorem k91cf3_end_ne_zero {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) {V : Type}
    [AddCommGroup V] [Module (ZMod q) V] [Nontrivial V] :
    (10800 : Module.End (ZMod q) V) * 3 ≠ 0 := by
  intro h0
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have h1 : (32400 : ℕ) • w = 0 := by
    simpa [smul_smul] using congrArg (fun f : Module.End (ZMod q) V => f w) h0
  rw [← Nat.cast_smul_eq_nsmul (ZMod q)] at h1
  have := Fact.mk hq
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact k91cf3_not_dvd hq hq7 ((ZMod.natCast_eq_zero_iff _ _).1 h2)
  · exact hw h2

theorem exists_fixed_model3_of_char (hD : IdentD) (he3 : e3 ^ 5 = 1) {q : ℕ} (hq : q.Prime)
    (hq7 : 7 ≤ q) {V : Type} [AddCommGroup V] [Module (ZMod q) V] [Nontrivial V]
    (ρ : model3 →* Module.End (ZMod q) V) (h : 1 + ρ c3 + ρ c3 ^ 2 = 0) :
    ∃ v : V, v ≠ 0 ∧ ρ e3 v = v := by
  obtain ⟨T, v, hTv⟩ := hD
  have hP : ∑ m ∈ Finset.range 5, ρ e3 ^ m ≠ 0 := by
    intro hP0
    have key := hTv (Module.End (ZMod q) V) ρ
    simp only [hP0, mul_zero, zero_mul, List.map_const', List.sum_replicate, smul_zero] at key
    rw [k91cf3_two_sub_eq_three h] at key
    exact k91cf3_end_ne_zero hq hq7 key.symm
  exact exists_fixed_of_sum_pow_ne_zero (ρ e3) (by rw [← map_pow, he3, map_one]) hP

private theorem k91cf6_two_sub_eq_three {R : Type*} [Ring R] {x : R} (h : 1 + x + x ^ 2 = 0) :
    2 - x - x ^ 2 = 3 := by
  have h1 : (1 : R) + (x + x ^ 2) = 0 := by rwa [← add_assoc]
  rw [sub_sub, eq_neg_of_add_eq_zero_right h1, sub_neg_eq_add, two_add_one_eq_three]

private theorem k91cf6_not_dvd {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) : ¬ q ∣ 64800 := by
  intro hd
  have hle : ∀ {m n : ℕ}, 0 < m → q ∣ m ^ n → q ≤ m := fun hm hmn =>
    Nat.le_of_dvd hm (hq.dvd_of_dvd_pow hmn)
  rcases hq.dvd_mul.1 (show q ∣ 2 ^ 5 * 3 ^ 4 * 5 ^ 2 from hd) with h | h
  · rcases hq.dvd_mul.1 h with h | h
    · exact absurd (hle (by omega) h) (by omega)
    · exact absurd (hle (by omega) h) (by omega)
  · exact absurd (hle (by omega) h) (by omega)

private theorem k91cf6_end_ne_zero {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) {V : Type}
    [AddCommGroup V] [Module (ZMod q) V] [Nontrivial V] :
    (21600 : Module.End (ZMod q) V) * 3 ≠ 0 := by
  intro h0
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have h1 : (64800 : ℕ) • w = 0 := by
    simpa [smul_smul] using congrArg (fun f : Module.End (ZMod q) V => f w) h0
  rw [← Nat.cast_smul_eq_nsmul (ZMod q)] at h1
  have := Fact.mk hq
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact k91cf6_not_dvd hq hq7 ((ZMod.natCast_eq_zero_iff _ _).1 h2)
  · exact hw h2

theorem exists_fixed_model6_of_char (hE : IdentE) (he6 : e6 ^ 5 = 1) {q : ℕ} (hq : q.Prime)
    (hq7 : 7 ≤ q) {V : Type} [AddCommGroup V] [Module (ZMod q) V] [Nontrivial V]
    (ρ : model6 →* Module.End (ZMod q) V) (h : 1 + ρ z6 + ρ z6 ^ 2 = 0) :
    ∃ v : V, v ≠ 0 ∧ ρ e6 v = v := by
  obtain ⟨T, v, hTv⟩ := hE
  have hP : ∑ m ∈ Finset.range 5, ρ e6 ^ m ≠ 0 := by
    intro hP0
    have key := hTv (Module.End (ZMod q) V) ρ
    simp only [hP0, mul_zero, zero_mul, List.map_const', List.sum_replicate, smul_zero] at key
    rw [k91cf6_two_sub_eq_three h] at key
    exact k91cf6_end_ne_zero hq hq7 key.symm
  exact exists_fixed_of_sum_pow_ne_zero (ρ e6) (by rw [← map_pow, he6, map_one]) hP

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
