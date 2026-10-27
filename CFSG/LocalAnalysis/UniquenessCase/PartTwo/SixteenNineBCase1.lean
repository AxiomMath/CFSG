module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case1_pRank_lt (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h1 : Case168_1 D V₀ V hV L) : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) < 3 := by
  obtain ⟨⟨e⟩, -⟩ := h1
  refine s16n9b_pRank_lt_of_not_dvd Nat.prime_three ?_
  rw [Nat.card_congr e.toEquiv]
  rcases CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.card_mulAut_six with h | h <;>
    rw [h] <;> decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
