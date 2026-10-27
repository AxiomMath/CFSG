module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.GroupTheory.WeirSylow.UniqueE27Linear
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.GroupTheory.WeirSylow.UniqueE27Unitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open CFSG.GroupTheory CFSG.GroupTheory.WeirSylow
open CFSG.Blueprint (LieModel)

theorem uniqueElemSylow_of_lieModel_psp {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .PSp 3 r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact fun h3 => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  exact (uniqueElemSylow_statedProj_statedSp_three K h3).of_mulEquiv e.symm

theorem uniqueElemSylow_of_lieModel_psl {X : Type} [Group X] {n r f : ℕ} (hn : n = 6 ∨ n = 7)
    (hq : r ^ f % 3 = 2) (h : LieModel X .PSL n r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact (uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K (by rwa [hK]) hn).of_mulEquiv
    e.symm

theorem uniqueElemSylow_of_lieModel_psu {X : Type} [Group X] {n r f : ℕ} (hn : n = 6 ∨ n = 7)
    (hq : r ^ f % 3 = 1) (h : LieModel X .PSU n r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  exact (uniqueElemSylow_statedProj_statedSU_of_mod_three_eq_one K hK hq hn).of_mulEquiv e.symm

theorem uniqueElemSylow_of_lieModel_pomegaOdd {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaOdd 3 r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact fun h3 => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hr.odd_of_ne_two hadm.2.2.2).pow
  exact (uniqueElemSylow_statedProj_statedOmega_quadOdd_three K hodd h3).of_mulEquiv e.symm

theorem uniqueElemSylow_of_lieModel_pomegaMinus {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaMinus 4 r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact fun h3 => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  exact (uniqueElemSylow_statedProj_statedOmega_quadMinus_four K hbc h3).of_mulEquiv e.symm

theorem uniqueElemSylow_of_isLieFam811 {X : Type} [Group X] {fam : LieFam811} {r f : ℕ}
    (h : IsLieFam811 X fam r f) (hfam : fam ≠ .l4) : UniqueElemSylow 3 3 X := by
  cases fam with
  | psp6 => exact uniqueElemSylow_of_lieModel_psp h.2.1 h.2.2
  | omega7 => exact uniqueElemSylow_of_lieModel_pomegaOdd h.2.2.1 h.2.2.2
  | pomega8m => exact uniqueElemSylow_of_lieModel_pomegaMinus h.2.1 h.2.2
  | l4 => exact absurd rfl hfam
  | l6 =>
    rcases h.2 with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact uniqueElemSylow_of_lieModel_psl (Or.inl rfl) hq hm
    · exact uniqueElemSylow_of_lieModel_psu (Or.inl rfl) hq hm
  | l7 =>
    rcases h.2 with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact uniqueElemSylow_of_lieModel_psl (Or.inr rfl) hq hm
    · exact uniqueElemSylow_of_lieModel_psu (Or.inr rfl) hq hm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
