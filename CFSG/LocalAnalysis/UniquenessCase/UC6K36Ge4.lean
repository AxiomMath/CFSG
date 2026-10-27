module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36FrameThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (Star36)

@[expose] def K36LtStar (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → CFSG.Open.IsKGroup Y →
    ∀ (M : Subgroup Y) (p : ℕ) (E : Subgroup Y), Hyp36 Y M p E → Star36 Y → K36Concl M p

@[expose] def K36EqlStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (M : Subgroup G) (p : ℕ) (E : Subgroup G), Hyp36 G M p E → Star36 G →
      ∀ L : Subgroup G, L.Normal → CFSG.IsComponent L → ⁅L, pCoreOf 2 M⁆ ≠ ⊥ →
        E ⊔ pCoreOf 2 M ⊔ L = ⊤ → K36Concl M p

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem oracle_of_ltStar (IH : K36LtStar (Nat.card G)) (hK : CFSG.Open.IsKGroup G) (hS : Star36 G) :
    Oracle36 M E p where
  conclIn X hXtop hEX hXM hQX hSX := by
    have hlt : Nat.card X < Nat.card G := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hXtop)
      rwa [Subgroup.card_top] at this
    exact K36Concl.toConclIn (IH ↥X hlt (hK.subgroup X) _ p _ (h.subgroupOf hEX hXM hQX) hSX)
  star_comp K hKc hne := h.star36_comp hS hKc hne
  star_cent Λ hΛ := by
    haveI := hΛ
    exact h.star36_cent_or_le hS Λ

end Hyp36

theorem k36LtStar_of_eql (hE : K36EqlStar) (hOF : L34OuterFree) : ∀ n : ℕ, K36LtStar n := by
  intro n
  induction n with
  | zero =>
    intro Y _ _ hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro Y _ _ hlt hK M p E h hS
    by_cases hn : Nat.card Y < n
    · exact ih Y hn hK M p E h hS
    · have hcard : Nat.card Y = n := by omega
      have IH : K36LtStar (Nat.card Y) := hcard ▸ ih
      have O := h.oracle_of_ltStar IH hK hS
      have hframe : K36Concl M p ∨ ∃ L : Subgroup Y, L.Normal ∧ CFSG.IsComponent L ∧
          ⁅L, pCoreOf 2 M⁆ ≠ ⊥ ∧ E ⊔ pCoreOf 2 M ⊔ L = ⊤ := by
        by_cases h4 : 3 < twoLocalPrimeRank 3 Y
        · exact h.frame_312_three O hS h4 hOF
        · exact h.frame_312_of_oracle O (not_lt.1 h4) hOF
      rcases hframe with hc | ⟨L, hL, hLc, hne, hX⟩
      · exact hc
      · exact hE Y hK M p E h hS L hL hLc hne hX

theorem k36_of_eqlStar (hE : K36EqlStar) (hOF : L34OuterFree) : K36 := by
  intro G _ _ hG M hM hQ p hp hp2 E hEel hEc hΓ hcal hstar
  exact k36LtStar_of_eql hE hOF (Nat.card G + 1) G (Nat.lt_succ_self _) hG M p E
    ⟨hM, hQ, hp, hp2, hEel, hEc, hΓ, hcal⟩ hstar

end CFSG.LocalAnalysis.UniquenessCase.UCK
