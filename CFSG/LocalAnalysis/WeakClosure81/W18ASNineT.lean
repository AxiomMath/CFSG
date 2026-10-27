module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineShape
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.Blueprint (LieModel OddLieType)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

theorem Socle185Shape.finite {T : Type} [Group T] (h : Socle185Shape T) : Finite T := by
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | h
  · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel hS
  · rcases h with ⟨-, -, hS⟩ | ⟨-, -, hS⟩
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel
        (hS.statedClassicalModel (by decide))
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel
        (hS.statedClassicalModel (by decide))
  · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel h

theorem Socle185Shape.oddLieType {T : Type} [Group T] (h : Socle185Shape T) : OddLieType T := by
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | h
  · exact ⟨.PSL, 2, p, e, hp, by omega, hS.1, Or.inl ⟨by decide, hS⟩⟩
  · rcases h with ⟨-, -, hS⟩ | ⟨-, -, hS⟩
    · exact ⟨.PSL, 3, p, f, hp, by omega, hS.admissible, hS⟩
    · exact ⟨.PSU, 3, p, f, hp, by omega, hS.admissible, hS⟩
  · exact ⟨.PSL, 2, 7, 1, by norm_num, by norm_num, h.1, Or.inl ⟨by decide, h⟩⟩

theorem Socle185Shape.card_cases (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Socle185Shape T) :
    (∃ q : ℕ, 11 ≤ q ∧ Odd q ∧ 2 * Nat.card T = q * ((q - 1) * (q + 1))) ∨
    (∃ q : ℕ, 11 ≤ q ∧ Odd q ∧ Nat.card T = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∨
    (∃ q : ℕ, 13 ≤ q ∧ Odd q ∧ Nat.card T = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) ∨
    Nat.card T = 168 := by
  rcases h with ⟨p, e, hp, hp5, he, hS⟩ | ⟨p, f, hp, hp5, h⟩ | h
  · left
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
    have hqodd : Odd (p ^ e) := hpodd.pow
    obtain ⟨-, hM, -⟩ := hO T .PSL 2 p e hS.1 (Or.inl ⟨by decide, hS⟩)
    refine ⟨p ^ e, ?_, hqodd, CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd
      (by omega) hqodd hM⟩
    have := Nat.odd_iff.mp hqodd
    omega
  · rcases h with ⟨h3, h4, hS⟩ | ⟨h3, h4, hS⟩
    · right; left
      obtain ⟨-, hM, -⟩ := hO T .PSL 3 p f hS.admissible hS
      have hgcd : lieOrderDivisor .PSL 3 (p ^ f) = 1 := by
        show Nat.gcd 3 (p ^ f - 1) = 1
        refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
        omega
      rw [hgcd, mul_one] at hM
      refine ⟨p ^ f, by omega, Nat.odd_iff.mpr (by omega), ?_⟩
      rw [hM]
      simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]
    · right; right; left
      obtain ⟨-, hM, -⟩ := hO T .PSU 3 p f hS.admissible hS
      have hpf : 5 ≤ p ^ f := hp5.trans (Nat.le_self_pow (by have := hS.admissible.2.1; omega) p)
      have hgcd : lieOrderDivisor .PSU 3 (p ^ f) = 1 := by
        show Nat.gcd 3 (p ^ f + 1) = 1
        refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
        omega
      rw [hgcd, mul_one] at hM
      refine ⟨p ^ f, by omega, Nat.odd_iff.mpr (by omega), ?_⟩
      rw [hM]
      have h3e : ¬ Even (3 : ℕ) := by decide
      simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair, h3e]
  · right; right; right
    obtain ⟨-, hM, -⟩ := hO T .PSL 2 7 1 h.1 (Or.inl ⟨by decide, h⟩)
    have := CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd (q' := 7)
      (by norm_num) (by decide) hM
    omega

theorem Socle185Shape.two_dvd_card (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Socle185Shape T) : 2 ∣ Nat.card T := by
  rcases h.card_cases hO with ⟨q, hq, hodd, hM⟩ | ⟨q, hq, hodd, hM⟩ | ⟨q, hq, hodd, hM⟩ | hM
  · obtain ⟨a, rfl⟩ := hodd
    have h2 : 2 * Nat.card T = 2 * (2 * ((2 * a + 1) * (a * (a + 1)))) := by
      rw [hM, show 2 * a + 1 - 1 = 2 * a by omega]
      ring
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h2) ▸ dvd_mul_right _ _
  · have : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
    rw [hM]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (even_iff_two_dvd.mp this) _) _
  · have : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
    rw [hM]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (even_iff_two_dvd.mp this) _) _
  · rw [hM]
    norm_num

private theorem mono_cube (s a : ℕ) (h : s ≤ a) :
    (s + 1) * (s * (s + 2)) ≤ (a + 1) * (a * (a + 2)) :=
  Nat.mul_le_mul (by omega) (Nat.mul_le_mul h (by omega))

theorem Socle185Shape.card_facts (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Socle185Shape T) :
    168 ≤ Nat.card T ∧ ¬ Nat.card T ∣ 720 ∧ Nat.card T ≠ 20160 ∧ Nat.card T ≠ 25920 ∧
      Nat.card T ≠ 3265920 := by
  rcases h.card_cases hO with ⟨q, hq, hodd, hM⟩ | ⟨q, hq, hodd, hM⟩ | ⟨q, hq, hodd, hM⟩ | hM
  · obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    have hM' : 2 * Nat.card T = (s + 1) * (s * (s + 2)) := by
      rw [hM, show s + 1 - 1 = s by omega, show s + 1 + 1 = s + 2 by omega]
    have hs : 10 ≤ s := by omega
    have h1320 : 11 * (10 * 12) ≤ (s + 1) * (s * (s + 2)) := by
      have := mono_cube 10 s hs
      simpa using this
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · intro hd
      have hle : Nat.card T ≤ 720 := Nat.le_of_dvd (by norm_num) hd
      have hs10 : s = 10 := by
        by_contra hne
        have hs2 : s % 2 = 0 := by
          have := Nat.odd_iff.mp hodd
          omega
        have h12 : 12 ≤ s := by omega
        have := mono_cube 12 s h12
        omega
      subst hs10
      have : Nat.card T = 660 := by omega
      rw [this] at hd
      exact absurd hd (by decide)
    · intro hc
      rcases le_or_gt s 33 with hl | hl
      · have := mono_cube s 33 hl
        omega
      · have := mono_cube 34 s hl
        omega
    · intro hc
      rcases le_or_gt s 36 with hl | hl
      · have := mono_cube s 36 hl
        omega
      · have := mono_cube 37 s hl
        omega
    · intro hc
      rcases le_or_gt s 185 with hl | hl
      · have := mono_cube s 185 hl
        omega
      · have := mono_cube 186 s hl
        omega
  · have h3 : 11 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 11 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3' : 11 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h3 1
    have hbig : 11 ^ 3 * ((11 ^ 2 - 1) * (11 ^ 3 - 1)) ≤ Nat.card T := by
      rw [hM]
      exact Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h3')
    norm_num at hbig
    refine ⟨by omega, fun hd => ?_, by omega, by omega, by omega⟩
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  · have h3 : 13 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 13 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3' : 13 ^ 3 + 1 ≤ q ^ 3 + 1 := Nat.add_le_add_right h3 1
    have hbig : 13 ^ 3 * ((13 ^ 2 - 1) * (13 ^ 3 + 1)) ≤ Nat.card T := by
      rw [hM]
      exact Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h3')
    norm_num at hbig
    refine ⟨by omega, fun hd => ?_, by omega, by omega, by omega⟩
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  · rw [hM]
    refine ⟨le_rfl, by decide, by decide, by decide, by decide⟩

theorem Socle185Shape.crossChar (hO : LieOrderFormulasInput) {T : Type} [Group T]
    (h : Socle185Shape T) {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : Nat.card T * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) := by
  obtain ⟨t', n', p, g, -, hp2, hadm', hY⟩ := h.oddLieType
  exact CFSG.SeitzReduction.CrossChar.eq_of_crossChar_arith
    (CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hp2 hM
      (hO T t' n' p g hadm' hY).2.1)

private theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h2 : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact Nat.Even.sub_odd (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

private theorem odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) :=
  (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one

theorem lieOrderDivisor_psl_two_two_pow {n : ℕ} (hn : 1 ≤ n) :
    lieOrderDivisor .PSL 2 (2 ^ n) = 1 :=
  Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn)

theorem lieOrderDivisor_psl_four_two_pow {n : ℕ} (hn : 1 ≤ n) :
    lieOrderDivisor .PSL 4 (2 ^ n) = 1 := by
  have h : Nat.Coprime (2 ^ 2) (2 ^ n - 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn))
  exact h

theorem lieOrderDivisor_psu_four_two_pow {n : ℕ} (hn : 1 ≤ n) :
    lieOrderDivisor .PSU 4 (2 ^ n) = 1 := by
  have h : Nat.Coprime (2 ^ 2) (2 ^ n + 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_two_pow_add_one hn))
  exact h

theorem lieOrderDivisor_psp_two_pow (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    lieOrderDivisor .PSp k (2 ^ n) = 1 :=
  Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn)

end CFSG.LocalAnalysis.WeakClosure81

end
