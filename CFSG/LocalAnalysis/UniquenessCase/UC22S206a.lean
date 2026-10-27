module

public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieSylowExponent
  lieOrderNumerator lieOrderDivisor)

theorem uc22s206a_card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem uc22s206a_card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem uc22s206a_factorization_two {k m : ℕ} (hm : Odd m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  rw [Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm2, add_zero]

theorem uc22s206a_eq_of_sylowExp_six {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hf : 2 < f) (h : lieSylowExponent t n * f = 6) :
    (t = .PSL ∧ n = 2 ∧ f = 6) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) := by
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 2 := by
      by_contra hc
      have : 3 * 3 ≤ n * (n - 1) / 2 * f := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hn2 : n = 2 := by
      by_contra hne
      have : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    subst hn2
    exact Or.inl ⟨rfl, rfl, by norm_num at h; omega⟩
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have h6 : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : 3 * 3 ≤ n * (n - 1) / 2 * f := Nat.mul_le_mul (by omega) (by omega)
    omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [lieSylowExponent] at h
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have : 4 * 3 ≤ n ^ 2 * f := Nat.mul_le_mul h4 (by omega)
    omega
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : 12 * 3 ≤ n * (n - 1) * f := Nat.mul_le_mul (by omega) (by omega)
    omega
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [lieSylowExponent] at h
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : 12 * 3 ≤ n * (n - 1) * f := Nat.mul_le_mul (by omega) (by omega)
    omega
  case twistedB2 =>
    obtain ⟨-, -, hn0, -⟩ := hadm
    simp only [lieSylowExponent] at h
    exact Or.inr ⟨rfl, hn0, by omega⟩
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals (simp only [lieSylowExponent] at h; omega)

theorem uc22s206a_not_listA_alt9 (hO : LieOrderFormulasInput) {Λ : Type} [Group Λ]
    (e : Λ ≃* alternatingGroup (Fin 9)) : ¬ Asc1930ListA Λ := by
  have hc : Nat.card Λ = 181440 := (Nat.card_congr e.toEquiv).trans uc22s206a_card_alt9
  have h2 : ∀ {t : StatedLieTag} {n f : ℕ}, LieModel Λ t n 2 f →
      lieSylowExponent t n * f = 6 := by
    intro t n f h
    obtain ⟨-, -, h2⟩ := hO Λ t n 2 f (CFSG.Blueprint.LieModel.admissible h) h
    have h181 : (181440 : ℕ) = 2 ^ 6 * 2835 := by norm_num
    have hodd : Odd (2835 : ℕ) := ⟨1417, by norm_num⟩
    rw [hc, h181, uc22s206a_factorization_two hodd] at h2
    exact h2.symm
  rintro ⟨n, ⟨k, rfl⟩, hn1, h | h | h⟩
  · have := h2 h
    simp only [lieSylowExponent] at this
    omega
  · have := h2 h
    simp only [lieSylowExponent] at this
    omega
  · have := h2 h
    simp only [lieSylowExponent] at this
    obtain rfl : k = 1 := by omega
    obtain ⟨-, hM, -⟩ := hO Λ _ _ _ _ (CFSG.Blueprint.LieModel.admissible h) h
    rw [hc] at hM
    revert hM
    decide

theorem uc22s206a_not_listB_alt8 (hO : LieOrderFormulasInput) {Λ : Type} [Group Λ]
    (e : Λ ≃* alternatingGroup (Fin 8)) : ¬ Asc1930ListB Λ := by
  have hc : Nat.card Λ = 20160 := (Nat.card_congr e.toEquiv).trans uc22s206a_card_alt8
  have h2 : ∀ {t : StatedLieTag} {n f : ℕ}, LieModel Λ t n 2 f →
      lieSylowExponent t n * f = 6 := by
    intro t n f h
    obtain ⟨-, -, h2⟩ := hO Λ t n 2 f (CFSG.Blueprint.LieModel.admissible h) h
    have h201 : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
    have hodd : Odd (315 : ℕ) := ⟨157, by norm_num⟩
    rw [hc, h201, uc22s206a_factorization_two hodd] at h2
    exact h2.symm
  rintro (⟨t, m, n, hn, h⟩ | h | h | h | h | h | he)
  · obtain ⟨-, hM, -⟩ := hO Λ _ _ _ _ (CFSG.Blueprint.LieModel.admissible h) h
    rw [hc] at hM
    rcases uc22s206a_eq_of_sylowExp_six (CFSG.Blueprint.LieModel.admissible h) hn (h2 h) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · revert hM
      decide
    · revert hM
      decide
  · have := h2 h
    revert this
    decide
  · have := h2 h
    revert this
    decide
  · have := h2 h
    revert this
    decide
  · have := h2 h
    revert this
    decide
  · have := h2 h
    revert this
    decide
  · obtain ⟨e'⟩ := he
    have h9 := (Nat.card_congr e'.toEquiv).trans uc22s206a_card_alt9
    omega

theorem uc22s206a_isCoatom_stabilizer (i : Fin 9) :
    IsCoatom (MulAction.stabilizer (alternatingGroup (Fin 9)) i) := by
  have h3 : 3 ≤ Nat.card (Fin 9) := by rw [Nat.card_fin]; norm_num
  haveI := alternatingGroup.isPreprimitive_of_three_le_card (Fin 9) h3
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (alternatingGroup (Fin 9)) i

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
