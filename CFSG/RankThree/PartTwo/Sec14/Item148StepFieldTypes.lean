module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepRank
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KF148FieldChar : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → Group.IsPerfect X →
    Sec4.IsoLThreePi X 2 n →
    ∀ (p f : ℕ) [Fact p.Prime], 1 ≤ f → IsLThreeEpsAt X p f → p = 2 ∧ f = n

theorem card_mul_gcd_of_isoLThreePi_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) :
    Nat.card X * Nat.gcd 3 (2 ^ n - 1) =
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ∨
      Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · left
    have h1 := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega)] at h1
    rw [Nat.card_congr φ.toEquiv]
    exact h1
  · right
    rw [Nat.card_congr φ.toEquiv]
    exact KFacts.KS14.card_projSU_three_mul_gcd 2 n hn

theorem card_ne_of_isoLThreePi_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) {N : ℕ} (hN : N = 2520 ∨ N = 1876896) : Nat.card X ≠ N := by
  intro hX
  have hg1 : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg2 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hQ : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hM1 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 ≤ (2 ^ n) ^ 3 := by nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hM2 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn7 : n ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have hQ8 : 256 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hlt)
    have hQ3 : 256 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hQ8 3
    rcases card_mul_gcd_of_isoLThreePi_two hn h with he | he <;> rw [hX] at he <;>
      rcases hN with rfl | rfl <;> nlinarith
  interval_cases n <;> rcases card_mul_gcd_of_isoLThreePi_two hn h with he | he <;>
    rw [hX] at he <;> rcases hN with rfl | rfl <;> norm_num at he

theorem isEmpty_mulEquiv_a7_of_isoLThreePi_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) : IsEmpty (X ≃* alternatingGroup (Fin 7)) := by
  refine ⟨fun φ => card_ne_of_isoLThreePi_two hn h (N := 2520) (Or.inl rfl) ?_⟩
  rw [Nat.card_congr φ.toEquiv]
  exact KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1

theorem isEmpty_mulEquiv_l37_of_isoLThreePi_two {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) (h7 : Fact (Nat.Prime 7)) :
    IsEmpty (X ≃* projSL 3 (GaloisField 7 1)) := by
  refine ⟨fun φ => card_ne_of_isoLThreePi_two hn h (N := 1876896) (Or.inr rfl) ?_⟩
  rw [Nat.card_congr φ.toEquiv]
  have h1 := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
  rw [GaloisField.card 7 1 (by norm_num)] at h1
  norm_num at h1
  omega

theorem kf148FieldTypes_of_char (h : KF148FieldChar) : KF148FieldTypes := by
  intro X _ _ n hn hP hX
  exact ⟨isEmpty_mulEquiv_a7_of_isoLThreePi_two hn hX,
    fun h7 => isEmpty_mulEquiv_l37_of_isoLThreePi_two hn hX h7,
    fun p f _ hf hL => h X n hn hP hX p f hf hL⟩

end CFSG.RankThree.PartTwo.Sec14
