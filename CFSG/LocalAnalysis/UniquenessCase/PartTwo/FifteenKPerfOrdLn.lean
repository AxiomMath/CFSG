module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s15k_pord_ln_card_eq {X K : Type} [Group X] [Field K] {n : ℕ}
    (hK : Nat.card K = 2) (e : X ≃* StatedProj (StatedSL n K)) :
    Nat.card X = Nat.card (StatedSL n K) := by
  have hscal : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [StatedAPI.statedScalars_eq_bot_of_card_two hK (Fin n), Subgroup.bot_subgroupOf]
  calc Nat.card X = Nat.card (StatedProj (StatedSL n K)) := Nat.card_congr e.toEquiv
    _ = Nat.card ((StatedSL n K) ⧸ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) := rfl
    _ = Nat.card ((StatedSL n K) ⧸ (⊥ : Subgroup (StatedSL n K))) := by rw [hscal]
    _ = Nat.card (StatedSL n K) := Nat.card_congr QuotientGroup.quotientBot.toEquiv

private theorem s15k_pord_ln_two_pow_seven_dvd_prod {n : ℕ} (h5 : 5 ≤ n) :
    (2 : ℕ) ^ 7 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have h3 : ((⟨3, by omega⟩ : Fin n) : ℕ) = 3 := rfl
  have h4 : ((⟨4, by omega⟩ : Fin n) : ℕ) = 4 := rfl
  have hne : (⟨3, by omega⟩ : Fin n) ≠ ⟨4, by omega⟩ := by
    intro h
    have : (3 : ℕ) = 4 := congrArg Fin.val h
    omega
  have hdvd3 : (2 : ℕ) ^ 3 ∣ 2 ^ n - 2 ^ ((⟨3, by omega⟩ : Fin n) : ℕ) := by
    rw [h3]
    exact Nat.dvd_sub (Nat.pow_dvd_pow 2 (by omega)) dvd_rfl
  have hdvd4 : (2 : ℕ) ^ 4 ∣ 2 ^ n - 2 ^ ((⟨4, by omega⟩ : Fin n) : ℕ) := by
    rw [h4]
    exact Nat.dvd_sub (Nat.pow_dvd_pow 2 (by omega)) dvd_rfl
  have hdvd34 : (2 : ℕ) ^ 3 * 2 ^ 4 ∣
      (2 ^ n - 2 ^ ((⟨3, by omega⟩ : Fin n) : ℕ)) *
        (2 ^ n - 2 ^ ((⟨4, by omega⟩ : Fin n) : ℕ)) :=
    mul_dvd_mul hdvd3 hdvd4
  have hprod : (2 ^ n - 2 ^ ((⟨3, by omega⟩ : Fin n) : ℕ)) *
      (2 ^ n - 2 ^ ((⟨4, by omega⟩ : Fin n) : ℕ)) ∣
        ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
    have h := Finset.prod_dvd_prod_of_subset
      ({⟨3, by omega⟩, ⟨4, by omega⟩} : Finset (Fin n)) Finset.univ
      (fun i : Fin n => 2 ^ n - 2 ^ (i : ℕ)) (Finset.subset_univ _)
    rwa [Finset.prod_pair hne] at h
  rw [show (2 : ℕ) ^ 7 = 2 ^ 3 * 2 ^ 4 by norm_num]
  exact dvd_trans hdvd34 hprod

theorem s15k_pord_ln {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n) (h : IsLn X n 1) :
    (n = 3 → Nat.card X = 168) ∧ (n = 4 → Nat.card X = 20160) ∧
      (5 ≤ n → 2 ^ 7 ∣ Nat.card X) := by
  have hn0 : n ≠ 0 := by omega
  have hsc := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn0 h
  rw [CFSG.Open.StatedClassicalModel] at hsc
  obtain ⟨-, K, hfield, hfin, hK, ⟨e⟩⟩ := hsc
  letI : Field K := hfield
  letI : Finite K := hfin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcard : Nat.card X = Nat.card (StatedSL n K) := s15k_pord_ln_card_eq hK2 e
  refine ⟨?_, ?_, ?_⟩
  · intro hn3
    rw [hcard, hn3, CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK2]
  · intro hn4
    rw [hcard, hn4, CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK2]
  · intro h5
    haveI : NeZero n := ⟨hn0⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
    rw [hcard, CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field, hq,
      show (2 : ℕ) - 1 = 1 by norm_num, Nat.div_one]
    exact s15k_pord_ln_two_pow_seven_dvd_prod h5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
