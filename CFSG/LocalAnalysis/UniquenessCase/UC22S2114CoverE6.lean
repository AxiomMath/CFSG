module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint (LieModel UntwistedChevalleyModel)

section Untwisted


theorem four_le_pRank_three_of_cover_E6_two {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : LieModel (Y ⧸ center Y) .E6 n 2 f) (h3 : 3 ∣ 2 ^ f - 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZ : 3 ∣ Nat.card (center Y)
  · have h6 := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerUntw Y n 2 f h h3).1 hZ
    omega
  · have hm : UntwistedChevalleyModel (Y ⧸ center Y) .E6 (2 ^ f) :=
      (h.chevalleyExceptionalModel (by decide)).2
    rw [← CFSG.SectionRank.pRank_quotient_eq (center Y) hZ]
    exact CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (by simp) hm

end Untwisted

section Twisted


theorem four_le_pRank_three_of_cover_twistedE6_two {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : LieModel (Y ⧸ center Y) .twistedE6 n 2 f) (h3 : 3 ∣ 2 ^ f + 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZ : 3 ∣ Nat.card (center Y)
  · have h6 := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6RankLowerTw Y n 2 f h h3).1 hZ
    omega
  · obtain ⟨-, hf, hm⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel h
    rw [← CFSG.SectionRank.pRank_quotient_eq (center Y) hZ]
    exact CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two hf hm

end Twisted

end CFSG.LocalAnalysis.UniquenessCase.UC22
