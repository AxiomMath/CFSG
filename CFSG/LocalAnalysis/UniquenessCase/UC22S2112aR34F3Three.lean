module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie
  (IsSmallThreeTag three_le_pRank_of_lieModel_odd)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_pRank_barInf_le_three (hS : Standing G) (S : Setup G) {L : Subgroup G}
    (hL : L ∈ calC S.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) :
    CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) ≤ 3 := by
  rw [← pRank_eq_pRank_barInf hp hpN]
  exact PartTwo.Three.pRank_le_three_dataOfSetup hS S hp hp2 hL.1.le

section Rank


theorem s21_12aFR34F3_dataOfSetup (hS : Standing G) (S : Setup G) {Ch : Choice2011 G} :
    S21_12aFR34F3 (dataOfSetup hS S) Ch := by
  intro _ _ L hL p hp hp2 t n f hadm ht hX _ _
  exfalso
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunManyType] at ht
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1) := by
    rintro ⟨rfl | rfl, rfl, -⟩ <;> simp [FunManyType] at ht
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    simp [FunManyType] at ht
  have hsm : ¬ IsSmallThreeTag t n := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩) <;> simp [FunManyType] at ht
  have hcl : (5 ≤ p ^ f ∧ ¬ (t = .PSL ∧ n = 2)) ∨ (p = 3 ∧ f = 1 ∧ ¬ IsSmallThreeTag t n) := by
    by_cases h5 : 5 ≤ p ^ f
    · exact Or.inl ⟨h5, hA1⟩
    · have hf : 1 ≤ f := hadm.2.1
      have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      have hp3 : p = 3 := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        omega
      subst hp3
      have hf1 : f = 1 := by
        by_contra hf1
        have h9 : 9 ≤ 3 ^ f :=
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact Or.inr ⟨rfl, hf1, hsm⟩
  have hpN := not_dvd_card_solvableRadical hL.2.2 hp hp2
    (uc22s2112r34_not_dvd_center_char hL hp hp2 hRee hX hcl)
  have h3 := uc22s2112r34_pRank_barInf_le_three hS S hL hp hp2 hpN
  obtain ⟨-, h4⟩ := three_le_pRank_of_lieModel_odd hp hp2 hX hA1 hA2 hRee
  rcases h4 with ⟨⟨rfl, rfl⟩ | rfl, -⟩ | h4
  · simp [FunManyType] at ht
  · simp [FunManyType] at ht
  · omega

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
