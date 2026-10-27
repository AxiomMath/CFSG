module

public import CFSG.RankThree.PartTwo.KFacts.KS21L44
public import CFSG.RankThree.PartTwo.KFacts.KS21Sp64
public import CFSG.RankThree.PartTwo.KFacts.KS21U58
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

theorem terminalTwoCentralInvolution_unfolded :
    ∀ (G : Type) [Group G] [Finite G] (I N : Subgroup G), I ≤ N →
      N ≤ Subgroup.normalizer (I : Set G) → IsTerminalGroup I → ∀ T : Sylow 2 N,
        ∃ z : I, orderOf z = 2 ∧ (z : G) ∈ (T : Subgroup N).map N.subtype ∧
          (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {(z : G)} ∧
          2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set I)) ∧
          ∃ H : Subgroup I, H ≤ Subgroup.centralizer ({z} : Set I) ∧ IsSimpleGroup H ∧
            3 ∣ Nat.card H ∧ Nat.card H ≠ 3 := by
  intro G _ _ I N hIN hN hI T
  have hL : HasLongRootSet I := by
    rcases hI with he | he | he <;> obtain ⟨e⟩ := he
    · exact U58.hasLongRootSet_projSU.of_mulEquiv e.symm
    · exact L44.hasLongRootSet_projSL.of_mulEquiv e.symm
    · exact Sp64.hasLongRootSet_projSp.of_mulEquiv e.symm
  obtain ⟨z, hzT, hTz, h2, hr, hH⟩ := exists_good_of_hasLongRootSet hIN hN hL T
  exact ⟨z, h2, hzT, hTz, hr, hH⟩

theorem terminalTwoCentralInvolution : TerminalTwoCentralInvolution :=
  terminalTwoCentralInvolution_unfolded

end CFSG.RankThree.PartTwo.KFacts.KS21
