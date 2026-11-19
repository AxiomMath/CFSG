module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRank
public import CFSG.Quasithin.EmptyFaithful.E111RFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open

theorem k_L2SzAutRank_holds : K_L2SzAutRank := by
  intro A _ _ L _ m _ hnab hC _ hLS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnab' : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnab ⟨⟨h⟩⟩
  have hAR : CFSG.Quasithin.E2.E22N.AutRankLe m ↥L := by
    rcases hLS with h | h
    · exact CFSG.Quasithin.E2.E22N.autRankLe_of_isPSL22 hnab'
        ((CFSG.Blueprint.LieModel.classical_iff (by decide)).1 h)
    · exact CFSG.Quasithin.E2.E22N.autRankLe_of_isSz hnab'
        (CFSG.Blueprint.LieModel.suzukiModel h).2
  exact (CFSG.LocalAnalysis.UniquenessCase.UCK.pRank_le_pRank_mulAut (p := 2) L hC).trans
    (CFSG.SectionRank.pRank_le one_lt_two fun E _ hE => hAR.2 E hE)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
