module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.GH74.Orders.LieType
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreTransfer
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (LieFam811 IsLie811)

theorem not_sq_dvd_ordA_six_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ CFSG.Open.ordA 6 2 := by
  rw [show CFSG.Open.ordA 6 2 = 2 ^ 21 * 3 ^ 4 * 7 ^ 2 * 19685 by decide]
  intro h
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 21 * 3 ^ 4 * 7 ^ 2) := by
    refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) <;>
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp (by norm_num)).2 (by omega))
  have h' : p ^ 2 ∣ 19685 := hcop.dvd_of_dvd_mul_left h
  have hle : p ≤ 140 := by nlinarith [Nat.le_of_dvd (by norm_num) h']
  interval_cases p <;> norm_num at h'

private theorem card_quotient_center_dvd_ordA_six_two {Y : Type} [Group Y] {fam : LieFam811}
    (hfam : fam = .l6 ∨ fam = .l7) (hY : IsLie811 Y fam 2 1) :
    Nat.card (Y ⧸ center Y) ∣ CFSG.Open.ordA 6 2 := by
  rcases hfam with rfl | rfl
  · obtain ⟨-, -, -, ⟨-, hm⟩ | ⟨h3, -⟩⟩ := hY
    · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hm]
      decide
    · norm_num at h3
  · obtain ⟨-, -, -, ⟨-, hm⟩ | ⟨h3, -⟩⟩ := hY
    · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hm]
      decide
    · norm_num at h3

theorem pRank_le_one_of_not_sq_dvd_card_quotient_center {Y : Type} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 2 ∣ Nat.card (Y ⧸ center Y)) : pRank p (⊤ : Subgroup Y) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Nat.Coprime (p ^ 2) (Nat.card (center Y)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2
      (CFSG.AGLEmbeddingD2.McLaughlin.not_dvd_card_center_of_perfect hY h))
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup Y)]
  refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hp fun hdvd => h ?_
  rw [Subgroup.card_top, Subgroup.card_eq_card_quotient_mul_card_subgroup (center Y)] at hdvd
  exact hZ.dvd_of_dvd_mul_right hdvd

theorem k7L67TwoSharp_holds : K7L67TwoSharp := by
  intro Y _ _ fam hfam hY p hp hp5 hp7
  exact pRank_le_one_of_not_sq_dvd_card_quotient_center (Group.isPerfect_def.1 hY.1.1) hp
    fun h => not_sq_dvd_ordA_six_two hp hp5 hp7
      (h.trans (card_quotient_center_dvd_ordA_six_two hfam hY))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
