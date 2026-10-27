module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
import CFSG.LocalAnalysis.UniquenessCase.UC6S898b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s17_45_rank_one_shapes {X : Type} [Group X] {n l : ℕ}
    (h : CHasLieRank X l n) (hl : l = 1) :
    IsL2 X n ∨ IsSz X n ∨ IsU3 X n := by
  obtain ⟨t, m, hadm, hmodel, hrank⟩ := h
  subst hl
  cases t with
  | PSL =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      have hm : m = 2 := by omega
      subst hm
      exact Or.inl hmodel
  | PSU =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      have hm : m = 3 := by omega
      subst hm
      exact Or.inr (Or.inr hmodel)
  | PSp =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      omega
  | POmegaOdd =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      omega
  | POmegaPlus =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      omega
  | POmegaMinus =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      omega
  | G2 =>
      simp only [CS17LieRank] at hrank
      omega
  | F4 =>
      simp only [CS17LieRank] at hrank
      omega
  | E6 =>
      simp only [CS17LieRank] at hrank
      omega
  | E7 =>
      simp only [CS17LieRank] at hrank
      omega
  | E8 =>
      simp only [CS17LieRank] at hrank
      omega
  | twistedE6 =>
      simp only [CS17LieRank] at hrank
      omega
  | trialityD4 =>
      simp only [CS17LieRank] at hrank
      omega
  | twistedB2 =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      obtain rfl : m = 0 := by omega
      exact Or.inr (Or.inl hmodel)
  | twistedG2 =>
      simp only [CS17LieRank] at hrank
      simp only [StatedLieAdmissible] at hadm
      omega
  | twistedF4 =>
      simp only [CS17LieRank] at hrank
      omega
  | Tits =>
      simp only [CS17LieRank] at hrank
      omega

theorem s17_45_su3_arithmetic {n : ℕ} (hpow : IsPowTwo n) (hn1 : n ≠ 1) :
    Even n ∧ ¬ 3 ∣ 2 ^ n + 1 ∧ ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ s ∣ 2 ^ n + 1 := by
  have heven : Even n := by
    obtain ⟨k, rfl⟩ := hpow
    exact Nat.even_pow.2 ⟨even_two, by rintro rfl; exact hn1 (pow_zero 2)⟩
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hpow
    exact pow_ne_zero k two_ne_zero
  obtain ⟨q, hq, hq3, hqdvd⟩ := UC6S898.exists_prime_gt_three_dvd (n := n)
    (by obtain ⟨m, hm⟩ := heven; omega) (by obtain ⟨m, hm⟩ := heven; omega)
  refine ⟨heven, UC6S898.not_three_dvd_two_pow_add_one_of_even heven, q, hq, ?_, hqdvd⟩
  have hq4 : q ≠ 4 := by
    rintro rfl
    exact (by norm_num : ¬ Nat.Prime 4) hq
  omega

theorem s17_45_su3_arithmetic_of_ctx {D : Data G} {V₀ V L X : Subgroup G} {n p l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (hC : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (h33 : R17_33_2At D V₀ V)
    (hshape : IsSU3 (Bar2 L) n) :
    Even n ∧ ¬ 3 ∣ 2 ^ n + 1 ∧ ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧ s ∣ 2 ^ n + 1 := by
  have hpow : IsPowTwo n := h33 L n hC.mem_calC hshape
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hadm : StatedLieAdmissible .PSU 3 2 1 :=
      CFSG.Blueprint.LieModel.admissible hshape.2
    simp only [StatedLieAdmissible] at hadm
    norm_num at hadm
  exact s17_45_su3_arithmetic hpow hn1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
