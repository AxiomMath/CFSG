module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwoK
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNK
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Conj3
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3ThinNN (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ¬ (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
    ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q → ∀ p ∈ D.sig, normalizer (X : Set G) ≤ D.M

theorem R847E3.normalizer_le_of_three_of_not_normal (hSE : StronglyEmbeddedFive)
    (hThin : PartTwo.ThinList13) (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hS : Standing G) (S : Setup G) (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G}
    (hY : Y ∈ calC S.M) (hYN : ¬ (Y.subgroupOf S.M).Normal) (hthin : F08.Thin8 Y)
    {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hXc : Nat.card X = q) : normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hrank : CFSG.Open.pRank q S.M ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 S.M
      (dataOfSetup hS S).maxLocal.1).trans (le_of_eq hS.rank)
  have hYM : Y ≤ S.M := hY.1.le
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  have hKY : CFSG.IsKGroup (Bar2 Y) :=
    uc22br4_isKGroup_catalog_of_open ((hK.of_le hYM).quotient (CFSG.pCore 2 ↥Y))
  obtain ⟨hs, ht⟩ := hThin (Bar2 Y) hKY hY.2.2 (PartTwo.s13_pCore_bar_eq_bot Y)
    fun r hr hr2 => PartTwo.s13_pRank_bar_le_one hthin hr hr2
  have := hs
  have hZ : center (Bar2 Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Bar2 Y)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := PartTwo.s13_nonabelian_bar hY
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab
  by_contra hN
  obtain ⟨E, hEM, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three (hSg.three_le 3 hp)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (normalizer (X : Set G) ⊓ S.M) := by
    by_cases hEN : E ≤ normalizer (Y : Set G)
    · exact R847E3.two_le_pRank_normalizer_inf Nat.prime_three (by norm_num) hq hYM hEM hEN
        hEel hEc (hthin 3 Nat.prime_three (by norm_num)) (hthin q hq hq2) hXY hXc
    have hF := uc22ine229c3_card_le_mul hY hq hq2 hXY hXc
      (by rw [hZ, Subgroup.card_bot]; exact hq.not_dvd_one) hrank hEM
    have hFY : E ⊓ normalizer (Y : Set G) ⊓ Y = ⊥ := by
      rw [eq_bot_iff, ← R847E3.inf_eq_bot_of_not_le_normalizer hY hZ Nat.prime_three
        (by norm_num) hEM hEel hEN]
      exact inf_le_inf_right Y inf_le_left
    refine R847E3.two_le_pRank_normalizer_inf_of_card Nat.prime_three (by norm_num) hq hYM
      (inf_le_left.trans hEM) inf_le_right (hEel.mono inf_le_left) ?_ (hthin q hq hq2) hXY hXc
    rw [hFY, Subgroup.card_bot, mul_one]
    rw [hEc, show (3 : ℕ) ^ 3 = 3 * 3 ^ 2 by norm_num] at hF
    exact Nat.le_of_mul_le_mul_left hF (by norm_num)
  have hH := uc22s13xm_sec7Hyp Nat.prime_three (by norm_num) hsp hX1 (hXY.trans hYM) hN h2
  obtain ⟨W, hW, π, hπ⟩ := R847E3.exists_le_normalizer_inf_surjective hY hYN hq hq2 hXY hXc
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY.2.1
  have hodd := PartOne.Section7.odd_card_pPrimeCore hsp Nat.prime_three
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp) hN h2
  have h35 := R847E3.eq_five_of_kf7Use (kf7Use_dataOfSetup hSQ hSE hK3 hS S) hp hH hW π hπ
    (even_iff_two_dvd.1 (R847E3.even_card_of_thin ht))
    fun h => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 h)
  omega

theorem r847E3ThinNN_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) : R847E3ThinNN (dataOfSetup hS S) := by
  intro Y hY hYN hthin X hXY q hq hq2 hXc p hp
  by_cases h3 : p = 3
  · subst h3
    exact R847E3.normalizer_le_of_three_of_not_normal hSE hThin hSQ hK3 hS S hp hY hYN hthin hXY
      hq hq2 hXc
  · exact r847E3ThinNNTwo_dataOfSetup hSE hSEZ hThin hSQ hK3 hG3 hRee hS S Y hY hYN hthin X hXY q
      hq hq2 hXc p hp fun h => absurd h h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
