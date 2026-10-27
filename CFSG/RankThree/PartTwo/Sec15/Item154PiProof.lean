module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofProper
public import CFSG.RankThree.PartTwo.Sec15.Item155R2Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem step155GrowAltTwoNHJWR_of_y4LThreePi (hπ : Y4LThreePiNHJR) : Step155GrowAltTwoNHJWR := by
  intro G _ _ A c L hR _ hNHJ X K Y M T hC _ _ _ _ _ htwo hpi _ _
  obtain ⟨n, -, hn, -, -, hXε, -⟩ := htwo
  exact (hpi ⟨n, hn, hπ G A c L hR hNHJ X (hC.res ▸ hC.isY.2.1) n hn hXε⟩).elim

theorem step155GrowAltTwoFieldWR_of_y4LThreePi (hπ : Y4LThreePiNHJR) :
    Step155GrowAltTwoFieldWR := by
  intro G _ _ A c L hR _ hNHJ X K Y M T hC _ _ _ _ _ htwo hpi _ _ _
  obtain ⟨n, -, hn, -, -, hXε, -⟩ := htwo
  exact (hpi ⟨n, hn, hπ G A c L hR hNHJ X (hC.res ▸ hC.isY.2.1) n hn hXε⟩).elim

section Pi

theorem step155GrowAltTwoWR_of_y4LThreePi (h148 : Item148R) (hbot : Item145BotS14)
    (hπ : Y4LThreePiNHJR) : Step155GrowAltTwoWR :=
  step155GrowAltTwoWR_of_nhj h148 hbot (step155GrowAltTwoNHJWR_of_y4LThreePi hπ)

theorem item154Pi_of_item154 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h154 : Item154 A (lB A) L)
    (hπ : ¬ AllPointsHJ A → ∀ X ∈ scriptY4 A (lB A), ∀ n : ℕ, 1 ≤ n →
      IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n → Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) :
    Sec16.Item154Pi A (lB A) L := by
  intro Y hY X hX hXY R hR
  rcases h154 Y hY X hX hXY R hR with h1 | ⟨n, m, hn, hm, hY', hXε, hL⟩ | h3
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨n, m, hn, hm, hY', hXε, ?_, hL⟩)
    by_cases hHJ : AllPointsHJ A
    · exact (Proof155w3.not_case154Two_of_allPointsHJ h h148 hbot hHJ hY.1
        ⟨n, m, hn, hm, hY', hXε, hL⟩).elim
    · exact ⟨2, n, ⟨Nat.prime_two⟩, hn, hπ hHJ X hX n hn hXε⟩
  · exact Or.inr (Or.inr h3)

theorem item154PiR_of_item154R (h148 : Item148R) (hbot : Item145BotS14) (h154 : Item154R)
    (hπ : Y4LThreePiNHJR) : Item154PiR :=
  fun G _ _ A c L hR => item154Pi_of_item154 hR.toSec14Std (h148 G A c L hR)
    (hbot G A c L hR.toSec14Std) (h154 G A c L hR) (hπ G A c L hR)

theorem item154PiR_of_steps
    (h148 : Item148R) (hbot : Item145BotS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift)
    (hD4 : Step148D4) (hσ : Step148KTypeSigma) (h154 : Item154R) : Item154PiR :=
  item154PiR_of_item154R h148 hbot h154
    (y4LThreePiNHJR_of h134 h48 hCore hPoint hKT hLift hD4 hσ)

theorem item154PiR_of_proper (h148 : Item148R) (hbot : Item145BotS14) (h154 : Item154ProperR)
    (hπ : Y4LThreePiNHJR) : Item154PiR :=
  item154PiR_of_item154R h148 hbot (item154R_of_proper h154) hπ

end Pi

end CFSG.RankThree.PartTwo.Sec15
