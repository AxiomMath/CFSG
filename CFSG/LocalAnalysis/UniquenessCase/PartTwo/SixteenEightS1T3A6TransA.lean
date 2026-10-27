module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 Matrix

variable {X : Type} [Group X]

private theorem s16t3_card_specialLinear_ne (K : Type) [Field K] [Finite K] (n : ℕ)
    (hK : Nat.card K = 2) : Nat.card (SpecialLinearGroup (Fin n) K) ≠ 360 := by
  by_cases hn : n ≤ 2
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl | rfl
    · haveI : IsEmpty (Fin 0) := ⟨Fin.elim0⟩
      haveI : Subsingleton (SpecialLinearGroup (Fin 0) K) := inferInstance
      have h1 : Nat.card (SpecialLinearGroup (Fin 0) K) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      omega
    · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K)
        (by norm_num : 1 ≤ 1), hK]
      decide
    · rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K)
        (by norm_num : 1 ≤ 2), hK]
      decide
  · have hn3 : 3 ≤ n := by omega
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K)
      (by omega : 1 ≤ n), hK]
    intro hc
    have hmem : 3 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨by norm_num, hn3⟩
    have h7 : 7 ∣ ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
      refine dvd_trans (show 7 ∣ 2 ^ 3 - 1 by norm_num) ?_
      exact Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) hmem
    have hdvd : 7 ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) :=
      dvd_mul_of_dvd_right h7 _
    rw [hc] at hdvd
    norm_num at hdvd

private theorem s16t3_card_statedSp_ne (K : Type) [Field K] [Finite K] (r : ℕ)
    (hK : Nat.card K = 2) : Nat.card (StatedSp r K) ≠ 360 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) r, hK]
  by_cases hr : r ≤ 2
  · have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hr' with rfl | rfl | rfl <;> decide
  · have hr3 : 3 ≤ r := by omega
    intro hc
    have hmem : 3 ∈ Finset.Icc 1 r := Finset.mem_Icc.mpr ⟨by norm_num, hr3⟩
    have h7 : 7 ∣ ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) := by
      refine dvd_trans (show 7 ∣ 2 ^ (2 * 3) - 1 by norm_num) ?_
      exact Finset.dvd_prod_of_mem (fun j => 2 ^ (2 * j) - 1) hmem
    have hdvd : 7 ∣ 2 ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) :=
      dvd_mul_of_dvd_right h7 _
    rw [hc] at hdvd
    norm_num at hdvd

theorem s16t3_card_ne_of_isSLn {n : ℕ} (h : IsSLn X n 1) : Nat.card X ≠ 360 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL]
  exact s16t3_card_specialLinear_ne K n hK2

theorem s16t3_card_ne_of_isSpn {n : ℕ} (h : IsSpn X n 1) : Nat.card X ≠ 360 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  rw [Nat.card_congr e.toEquiv]
  exact s16t3_card_statedSp_ne K (n / 2) hK2

theorem s16t3_card_of_isAlt_six (h : UC22.IsAlt X 6) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  haveI : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem s16t3_eq_six_of_isAlt_card {n : ℕ} (h : UC22.IsAlt X n) (hc : Nat.card X = 360) :
    n = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv] at hc
  by_cases hn : n ≤ 1
  · haveI : Subsingleton (Fin n) := ⟨fun a b => Fin.ext (by omega)⟩
    haveI : Subsingleton (alternatingGroup (Fin n)) :=
      ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
    have h1 : Nat.card (alternatingGroup (Fin n)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    omega
  · have hn2 : 2 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
    have hcard : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
    rw [hcard] at hc
    have h2 : 2 ∣ n.factorial := by
      simpa using Nat.factorial_dvd_factorial (m := 2) hn2
    have hfact : n.factorial = 720 := by
      have h1 := Nat.div_mul_cancel h2
      rw [hc] at h1
      norm_num at h1
      exact h1.symm
    by_cases hn6 : n ≤ 6
    · have hn' : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases hn' with rfl | rfl | rfl | rfl | rfl
      · norm_num at hfact
      · norm_num at hfact
      · norm_num at hfact
      · norm_num at hfact
      · rfl
    · have hn7 : 7 ≤ n := by omega
      have hle : Nat.factorial 7 ≤ n.factorial := Nat.factorial_le hn7
      rw [hfact] at hle
      norm_num at hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
