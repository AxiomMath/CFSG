module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem mem_uniqueSet_X (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D) : X ∈ uniqueSet D.M :=
  CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le (h1421 L₁ L₂ X h).1 inf_le_left h.X_le_M

theorem normalizer_X_le (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D) :
    normalizer (X : Set G) ≤ D.M :=
  CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
    (mem_uniqueSet_X h h1421)

theorem normalizer_inf_le (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D) {L : Subgroup G}
    (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) :
    normalizer ((X ⊓ L : Subgroup G) : Set G) ≤ D.M := by
  have hmem : X ⊓ L ∈ uniqueSet D.M := by
    rcases hL with rfl | hL
    · exact (h1421 _ L₂ X h).1
    · rw [Set.mem_singleton_iff] at hL
      subst hL
      exact (h1421 L₁ _ X h).2
  exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hmem

theorem le_of_isStronglyPEmbedded (h : Hyp141 D L₁ L₂ X) (hs : IsStronglyPEmbedded 3 D.M)
    (h63 : UC6.R6_3 D) {H : Subgroup G} (hXH : X ≤ H) (hF : Fstar H = pCoreOf 2 H) :
    H ≤ D.M := by
  have hXM : X ≤ D.M := h.X_le_M
  have hX9 : Nat.card X = 9 := h.card_X
  have hX3 : IsPGroup 3 X := h.sylow.isPGroup
  have hΓ : rankThreeGamma 1 3 X ≤ D.M := by
    refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall (fun Q hQX hQ1 => ?_)
    have hQb : Q ≠ ⊥ := by
      obtain ⟨E, hEQ, -, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
      rintro rfl
      have hE : E = ⊥ := le_bot_iff.1 hEQ
      rw [hE, Subgroup.card_bot] at hEc
      have h3 : 3 ^ 1 ≤ 3 ^ CFSG.Open.pRank 3 (⊥ : Subgroup G) :=
        Nat.pow_le_pow_right (by norm_num) hQ1
      omega
    exact hs.normalizer_le hQb (hX3.to_le hQX) (hQX.trans hXM)
  have hU : UniqueMax D.M X :=
    h63 3 Nat.prime_three (by norm_num) X hXM h.isElemAbelian_X (by rw [hX9]; norm_num) hΓ
  have hH : H ≠ ⊥ := by
    rintro rfl
    have : X = ⊥ := le_bot_iff.1 hXH
    rw [this, Subgroup.card_bot] at hX9
    exact absurd hX9 (by norm_num)
  obtain ⟨N, hN, hHN⟩ := exists_isMaxTwoLocal_ge_of_fstar hF hH
  have hNmem : N ∈ calMOf X := ⟨hN, hXH.trans hHN⟩
  have hND : N = D.M := by
    have : N ∈ ({D.M} : Set (Subgroup G)) := hU ▸ hNmem
    exact Set.mem_singleton_iff.1 this
  exact hND ▸ hHN

theorem inf_eq_bot (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D) (hSg : UC6S846.SigmaStd D)
    (hperm : PermutesPair D.M L₁ L₂) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {Q : Subgroup G} (hQ : IsPGroup q Q) (hQM : ¬ Q ≤ D.M) : Q ⊓ D.M = ⊥ := by
  by_contra hW1
  have hWp : IsPGroup q (Q ⊓ D.M : Subgroup G) := hQ.to_le inf_le_left
  have hWM : Q ⊓ D.M ≤ D.M := inf_le_right
  have hNW : normalizer ((Q ⊓ D.M : Subgroup G) : Set G) ≤ D.M := by
    by_cases hq7 : q = 7
    · subst hq7
      haveI : Fact (Nat.Prime 7) := ⟨hq⟩
      exact (h.isStronglyPEmbedded_seven hSg).normalizer_le hW1 hWp hWM
    · have hn : Q ⊓ D.M ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) :=
        h.le_normalizer_of_isPGroup hperm hq hq2 hWp hWM
      have hn₁ : Q ⊓ D.M ≤ normalizer (L₁ : Set G) := hn.trans inf_le_left
      exact h.normalizer_le_of_acts_trivially h1422 (L := L₁) (Set.mem_insert _ _) hq hq2 hWp hW1
        hn₁ (acts_trivially_of_isPGroup h.shape₁ hq hq2 hq3 hq7 hWp hn₁)
  have hWQ : (Q ⊓ D.M : Subgroup G) < Q :=
    lt_of_le_of_ne inf_le_left fun hEq => hQM (hEq ▸ hWM)
  have hlt := lt_inf_normalizer hq hQ hWQ
  have hle : Q ⊓ normalizer ((Q ⊓ D.M : Subgroup G) : Set G) ≤ Q ⊓ D.M :=
    fun x hx => ⟨hx.1, hNW hx.2⟩
  exact absurd hlt (not_lt_of_ge hle)

theorem pRank_le_three_of_fstar (h : Hyp141 D L₁ L₂ X) {H : Subgroup G}
    (hF : Fstar H = pCoreOf 2 H) (hH : H ≠ ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    Open.pRank q H ≤ 3 :=
  h.pRank_le_three hq hq2 (UC6S846.isPGroup_pCoreOf H) (pCoreOf_ne_bot_of_fstar hF hH)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
