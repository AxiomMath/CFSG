module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

@[expose] def R875Comp {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → IsComponentOf X (H ⊓ D.M)

private theorem pRank_bot_eq_zero_of_prime {G : Type} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) : CFSG.Open.pRank q (⊥ : Subgroup G) = 0 := by
  refine Nat.le_antisymm ?_ (Nat.zero_le _)
  refine CFSG.SectionRank.pRank_le hq.one_lt fun E hE _ => ?_
  rw [le_bot_iff.1 hE, Subgroup.card_bot, pow_zero]

private theorem not_solvable_of_hyp869 {G : Type} [Group G] [Finite G] {D : Data G}
    {L X : Subgroup G} (h : Hyp869 D L X) : ¬ Group.IsSolvable ↥D.M := by
  rcases h.1 with hL | ⟨hLM, -, hprod⟩
  · exact UC6S846.not_solvable_of_mem_calC hL
  · obtain ⟨k, S, hS, hLset⟩ := hprod
    cases k with
    | zero =>
      intro _
      exact h.2.2.2 (by
        have hLbot : L = ⊥ := by
          apply le_antisymm ?_ bot_le
          intro x hx
          rw [← SetLike.mem_coe, hLset] at hx
          simpa using hx
        rw [hLbot]
        intro p hp _
        rw [pRank_bot_eq_zero_of_prime hp]
        omega)
    | succ k =>
      intro hs
      exact UC6S846.not_solvable_of_mem_calC (hS ⟨0, Nat.succ_pos k⟩) hs

theorem pRank_le_three_of_minCex {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h870 : R870 D) {L X H : Subgroup G} (h : MinCex869 D L X H)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hX : 1 < CFSG.Open.pRank q X) :
    CFSG.Open.pRank q D.M ≤ 3 := by
  by_contra hle
  simp only [not_le] at hle
  have h4 : 4 ≤ CFSG.Open.pRank q D.M := by omega
  have hqσ : q ∈ D.sig := hSg.four_mem q hq hq2 h4
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_hyp869 h.hyp
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M :=
    UC6S846.sp_of_mem_sig hSg hns hqσ
  exact h870 L X H h q hq hq2 hX hsp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
