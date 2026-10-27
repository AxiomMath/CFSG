module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki.PFchapter1section1

theorem twoRankAtLeastTwo_of_two_le_twoRank {F : Type} [Group F] [Finite F]
    (h : 2 ≤ twoRank F) : TwoRankAtLeastTwo F := by
  have hbdd := CFSG.TwoRankLowerBound.Helpers.twoRank_bddAbove F
  have hne : ({rank | ∃ elementary : Subgroup F, elementary ≤ ⊤ ∧
      IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank} : Set ℕ).Nonempty := by
    refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun x hx => ?_⟩, ?_⟩
    · rw [Subgroup.mem_bot.mp hx, one_pow]
    · simp
  obtain ⟨E, -, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  have hEcard' : Nat.card E = 2 ^ twoRank F := hEcard
  have h4 : 4 ≤ Nat.card E := by
    rw [hEcard']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ twoRank F := Nat.pow_le_pow_right (by norm_num) h
  exact BenderSuzuki.twoRankAtLeastTwo_of_injective E.subtype E.subtype_injective
    (twoRankAtLeastTwo_of_elementary_card_ge_four E hE h4)

theorem smallerR1Full_of_bender (G : Type) [Group G] [Finite G] :
    ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G → 2 ≤ twoRank F →
      (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F := by
  intro F _ _ _ hrank ⟨A, hA⟩
  exact rank_two_strongEmbedding_r1Full (twoRankAtLeastTwo_of_two_le_twoRank hrank) A hA

end CFSG.ShultStronglyClosedTI
