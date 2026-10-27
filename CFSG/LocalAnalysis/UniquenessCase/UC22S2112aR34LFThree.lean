module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie (three_le_pRank_of_lieModel_odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_l3_false_three (hS : Standing G) (S : Setup G) {L : Subgroup G}
    (hL : L ∈ calC S.M) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hm : LieModel (BarInf L) .PSL 3 p f ∨ LieModel (BarInf L) .PSU 3 p f) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : 5 ≤ p ^ f :=
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  have key : ∀ t : StatedLieTag, (t = .PSL ∨ t = .PSU) → LieModel (BarInf L) t 3 p f → False := by
    intro t ht hX
    have hRee : t ≠ .twistedG2 := by rcases ht with rfl | rfl <;> nofun
    have hA1 : ¬ (t = .PSL ∧ 3 = 2) := fun h => absurd h.2 (by norm_num)
    have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
      (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨hq, hA1⟩))
    have h3 := uc22s2112r34_pRank_barInf_le_three hS S hL hp hp2 hpN
    obtain ⟨-, h4⟩ := three_le_pRank_of_lieModel_odd hp hp2 hX hA1
      (fun h => by have := h.2.2; omega) hRee
    rcases h4 with ⟨-, h1⟩ | h4 <;> omega
  rcases hm with h | h
  · exact key .PSL (Or.inl rfl) h
  · exact key .PSU (Or.inr rfl) h

theorem s21_12aFR34L3_dataOfSetup_of_l3P (hS : Standing G) (S : Setup G) {Ch : Choice2011 G}
    (hP : S21_12aFR34L3P (dataOfSetup hS S) Ch) : S21_12aFR34L3 (dataOfSetup hS S) Ch := by
  intro hH c L hL p hp hp2 f hm hno hfaith
  have hf : 1 ≤ f := by rcases hm with h | h <;> exact h.admissible.2.1
  rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
  · exact hP hH c L hL p hp hp2 hm hno hfaith
  · exact (uc22s2112r34_l3_false_three hS S hL hp hp2 hf2 hm).elim

theorem uc22s2112r34_exc_three (hS : Standing G) (S : Setup G) {L : Subgroup G}
    (hL : L ∈ calC S.M) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : FunTwoType t n) (hq : 5 ≤ p ^ f) (hX : LieModel (BarInf L) t n p f) :
    ((t = .PSp ∧ n = 2) ∨ t = .G2) ∧ f = 1 ∧ 3 ≤ CFSG.Open.pRank p L := by
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunTwoType] at ht
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1) := by
    rintro ⟨rfl | rfl, rfl, -⟩ <;> simp [FunTwoType] at ht
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    simp [FunTwoType] at ht
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX (Or.inl ⟨hq, hA1⟩))
  have h3 := uc22s2112r34_pRank_barInf_le_three hS S hL hp hp2 hpN
  obtain ⟨h3', h4⟩ := three_le_pRank_of_lieModel_odd hp hp2 hX hA1 hA2 hRee
  rw [← pRank_eq_pRank_barInf hp hpN] at h3'
  rcases h4 with ⟨hexc, hf1⟩ | h4
  · exact ⟨hexc, hf1, h3'⟩
  · omega

theorem s21_12aFR34F2Sig_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G)
    {Ch : Choice2011 G} : S21_12aFR34F2Sig (dataOfSetup hS S) Ch := by
  intro _ _ L hL p hp hp2 hpσ t n f _ ht hq hX _ _
  exfalso
  obtain ⟨-, rfl, h3⟩ := uc22s2112r34_exc_three hS S hL hp hp2 ht (by omega) hX
  rw [pow_one] at hq
  exact hpσ (PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hp hq
    (h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
