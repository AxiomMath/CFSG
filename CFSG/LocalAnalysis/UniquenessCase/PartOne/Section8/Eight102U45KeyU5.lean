module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyAbstract
public import CFSG.Blueprint.Catalog
import CFSG.Adapters.LieModelUnitaryOuter
import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms

theorem le_one_of_pow_dvd_card_PSU_five {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (h : p ^ n ∣ 2 ^ 20 * 3 ^ 2 * 5 ^ 4 * (13 * 17 * 41)) : n ≤ 1 := by
  have hcopA : Nat.Coprime (p ^ n) (2 ^ 20 * 3 ^ 2 * 5 ^ 4) :=
    (((((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right 20).mul_right
      (((Nat.coprime_primes hp Nat.prime_three).2 hp3).pow_right 2)).mul_right
      (((Nat.coprime_primes hp Nat.prime_five).2 hp5).pow_right 4)).pow_left n
  have hB : p ^ n ∣ 13 * 17 * 41 := hcopA.dvd_of_dvd_mul_left h
  by_contra hn1
  have hn2 : 2 ≤ n := by omega
  have hp2B : p ^ 2 ∣ 13 * 17 * 41 := (pow_dvd_pow p hn2).trans hB
  have hpB : p ∣ 13 * 17 * 41 := by
    simpa using (pow_dvd_pow p (by norm_num : 1 ≤ 2)).trans hp2B
  have hp1341 : p = 13 ∨ p = 17 ∨ p = 41 := by
    rcases hp.dvd_mul.mp hpB with h | h
    · rcases hp.dvd_mul.mp h with h' | h'
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp h' with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact Or.inl h1
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp h' with h1 | h1
        · exact absurd h1 hp.ne_one
        · exact Or.inr (Or.inl h1)
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 41)).mp h with h1 | h1
      · exact absurd h1 hp.ne_one
      · exact Or.inr (Or.inr h1)
  rcases hp1341 with rfl | rfl | rfl
  · exact absurd hp2B (by norm_num)
  · exact absurd hp2B (by norm_num)
  · exact absurd hp2B (by norm_num)

theorem le_inner_of_isElemAbelian_of_lieModel_PSU_five {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 5 2 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp5 : p ≠ 5) {R : Subgroup (MulAut X)} (hR : IsElemAbelian p R) :
    R ≤ (MulAut.conj : X →* MulAut X).range := by
  intro α hα
  have hout : Nat.card (Outer X) = 20 := by
    rw [CFSG.Blueprint.LieModel.card_outer_psu hX (by norm_num) (by norm_num)]
    norm_num
  have hcop : Nat.Coprime p (Nat.card (Outer X)) := by
    rw [hout, show (20 : ℕ) = 2 ^ 2 * 5 by norm_num, hp.coprime_iff_not_dvd]
    intro h
    rcases hp.dvd_mul.mp h with h2 | h5
    · have h2' : p ∣ 2 := hp.dvd_of_dvd_pow h2
      rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h1 | h1
      · exact hp.ne_one h1
      · exact hp2 h1
    · rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h1 | h1
      · exact hp.ne_one h1
      · exact hp5 h1
  have h1 : (QuotientGroup.mk α : Outer X) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hR.2 α hα, QuotientGroup.mk_one]
  have h2 := pow_gcd_eq_one.2 ⟨h1, pow_card_eq_one' (G := Outer X)⟩
  rw [hcop.gcd_eq_one, pow_one] at h2
  exact (QuotientGroup.eq_one_iff (N := inner X) α).1 h2

theorem u45KeyConcl_of_lieModel_PSU_five {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 5 2 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) : U45KeyConcl X p := by
  classical
  refine u45KeyConcl_of_card_le ?_
  intro R hR
  have horder : Nat.card X = 2 ^ 20 * 3 ^ 2 * 5 ^ 4 * (13 * 17 * 41) := by
    obtain ⟨K, _, h, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.EvenBN.U5.exists_hypPSU_equiv (X := X) (f := 2) (by norm_num) hX
    rw [Nat.card_congr e.toEquiv]
    have hSU : Nat.card (hypSU h 2 1) = 4 ^ 10 * 254840625 := by
      have hprod : (∏ i ∈ Finset.Icc 2 5,
          (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i)) = (254840625 : ℤ) := by decide
      have hSU := (card_hypSU h (r := 2) (ε := 1) (by norm_num)).1
      rw [hprod] at hSU
      have h' : (Nat.card (hypSU h 2 1) : ℤ) = ((4 ^ 10 * 254840625 : ℕ) : ℤ) := by
        rw [hSU]
        norm_num
      exact_mod_cast h'
    have hZ : Nat.card (hypScalars h 2 1) = 5 := by
      have h := card_hypScalars h (r := 2) (ε := 1) (by norm_num)
      norm_num at h
      exact h
    have hPSU : Nat.card (hypPSU h 2 1) = 4 ^ 10 * 50968125 := by
      have hmul := card_hypPSU_mul h (r := 2) (ε := 1)
      rw [hSU, hZ] at hmul
      have h5 : Nat.card (hypPSU h 2 1) * 5 = (4 ^ 10 * 50968125) * 5 := by
        rw [hmul]
        norm_num
      exact Nat.mul_right_cancel (by norm_num : 0 < 5) h5
    rw [hPSU]
    norm_num
  have hdvdX : Nat.card R ∣ Nat.card X :=
    (Subgroup.card_dvd_of_le
      (le_inner_of_isElemAbelian_of_lieModel_PSU_five hX hp hp2 hp5 hR)).trans
      (Subgroup.card_range_dvd (MulAut.conj : X →* MulAut X))
  have hRpg : IsPGroup p R := fun x =>
    ⟨1, Subtype.ext (by simpa using hR.2 (x : MulAut X) x.2)⟩
  obtain ⟨m, hm⟩ := hRpg.exists_card_dvd_pow
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).mp hm
  have hnle : n ≤ 1 := le_one_of_pow_dvd_card_PSU_five hp hp2 hp3 hp5 (by
    rw [← horder, ← hn]
    exact hdvdX)
  calc Nat.card R = p ^ n := hn
    _ ≤ p := by
      have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with h0 | h1
      · rw [h0, pow_zero]
        exact le_of_lt hp.one_lt
      · rw [h1, pow_one]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
