module

public import CFSG.RankThree.PartOne.S12.Facts13

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem ne_of_card_E {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hE4 : Nat.card E = p ^ 4) : E ≠ A := by
  intro hEA
  rw [hEA, h.A_card] at hE4
  have := Nat.pow_right_injective (Nat.succ_le_of_lt h.prime.one_lt) hE4
  omega

@[expose] def Sec13Reinst : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroStarE p E, ∃ (B : Subgroup G) (c' : G),
      B ∈ admissibleTriples p E ∧ c' ∈ B ∧ c' ≠ 1 ∧ Sec12Hyp G p B c' X E ∧
      Sec12Facts G p B c' X E ∧ Sec13Facts G p B c' X E ∧
      ¬ Outcome152Five p E B (lieGenerated p E)

theorem sec13Reinst_of_nodes (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : Sec13Reinst := by
  intro G _ _ p A c L E h hF13 hT X hX
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate X hX
  have hT' : ¬ Outcome152Five p E B (lieGenerated p E) := by
    rintro ⟨f, hf, hpq, hiso, hrefl, hE4, -, heven⟩
    exact hT ⟨f, hf, hpq, hiso, hrefl, hE4, ne_of_card_E h hE4, heven⟩
  exact ⟨B, c', hB, hc'B, hc'1, h', hF',
    Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126 h127 h128 h129
      h' hT', hT'⟩

end CFSG.RankThree.PartOne.S13K
