module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoOrderFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_14K2TU4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, 4 ∣ f ∧ (IsSp4 (BarInf L) f ∨ IsG2 (BarInf L) f ∨ IsU4 (BarInf L) f ∨
        Is3D4 (BarInf L) f) ∧
      ∀ p ∈ D.sig, p ∣ 2 ^ f + 1 ∨ (Is3D4 (BarInf L) f ∧ p ∣ 2 ^ (2 * f) - 2 ^ f + 1)) →
    (∀ f : ℕ, 4 ∣ f → ¬ IsSp4 (BarInf L) f ∧ ¬ IsG2 (BarInf L) f ∧ ¬ Is3D4 (BarInf L) f) →
    D.k = 2 → 3 ≤ c.n → 4 ∣ c.n → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

@[expose] def S21_14D4TK1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    (∃ f : ℕ, Is3D4 (BarInf L) f) → (c.n = 3 ∨ c.n = 6) → D.k = 1 →
    (D.k = 1 → c.n = 3 ∧ c.B0 ≤ normalizer (D.T : Set G)) → c.B0 ≤ normalizer (L : Set G) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → (∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1

section SmallTriality

theorem three_mem_sig_of_is3D4_one {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h7σ : 7 ∉ D.sig) {L : Subgroup G} (h3D4 : Is3D4 (Bar2 L) 1)
    (hsig : ∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L) : 3 ∈ D.sig := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  by_contra h3
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ hp)
  have hp7 : p ≠ 7 := fun h => h7σ (h ▸ hp)
  have hsmall := PartTwo.Inputs1719.k_3D4TwoSmallRank_holds (Bar2 L) h3D4 p hpp hp2 hp3 hp7
  have hr := hsig p hp
  rw [← pRank_bar2_eq_of_odd hpp hp2] at hr
  omega

end SmallTriality

section

theorem s21_14D4T_of_r891 {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D)
    (h891 : ∀ L ∈ calC D.M, ∀ f : ℕ, 2 ≤ f → Is3D4 (Bar2 L) f →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hK1 : S21_14D4TK1 D Ch) : S21_14D4T D Ch := by
  intro hH c L hL hChev hpow hex hn hk1 hB0 hfaith hsig
  by_cases hk : D.k = 1
  · exact hK1 hH c L hL hChev hpow hex hn hk hk1 hB0 hfaith hsig
  · exfalso
    obtain ⟨f, hX⟩ := hex
    obtain ⟨e⟩ :=
      uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_is3D4 hL hX)
    have hD : Is3D4 (Bar2 L) f := CFSG.Blueprint.LieModel.of_mulEquiv e hX
    have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
      by_cases hf : f = 1
      · subst hf
        have h7 : 7 ∉ D.sig := uc22s2114_not_mem_sig hSg
          (UC6S846.not_solvable_of_mem_calC hL) hH c Nat.prime_seven (by
            rcases hn with hn | hn <;> rw [hn] <;> norm_num)
        exact UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL)
          (three_mem_sig_of_is3D4_one hSg h7 hD hsig)
      · have hf1 : 1 ≤ f := hD.admissible.2.1
        exact h891 L hL f (by omega) hD
    apply hk
    show CFSG.LocalAnalysis.RankThreeUC.kParam D.M = 1
    rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos hsp]

end

end CFSG.LocalAnalysis.UniquenessCase.UC22
