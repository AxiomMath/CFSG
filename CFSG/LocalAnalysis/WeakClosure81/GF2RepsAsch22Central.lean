module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
import CFSG.RankThree.PartOne.N143.T2CenSmall
import CFSG.RankThree.PartOne.N143.T2CenLie

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem pRank_quotient_le_three_of_central (hC5 : CFSG.AGLEmbedding.KFactCoverRankFive)
    (hNC : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentreRank)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hON : Nonempty (CFSG.Blueprint.NativeSporadic.ON ≃* TauCeti.SporadicName.ONan.Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hcat : CFSG.Open.IsCatalogGroup (Y ⧸ Subgroup.center Y))
    (hZ : IsPGroup p (Subgroup.center Y)) (hrk : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ Subgroup.center Y)) ≤ 3 ∨
      p = 3 ∧ Nonempty (Y ⧸ Subgroup.center Y ≃* CFSG.Blueprint.NativeSporadic.ON) := by
  by_cases hZ0 : Subgroup.center Y = ⊥
  · refine Or.inl ?_
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      ((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot)]
    exact hrk
  · by_cases hp3 : p = 3
    · subst p
      by_cases hcyc : IsCyclic (Subgroup.center Y)
      · rcases hW Y hq hcat hZ0 hZ hcyc hrk with
          ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
        · refine Or.inl ?_
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
          exact (CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_A6).trans (by norm_num)
        · refine Or.inl ?_
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
          exact (CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_A7).trans (by norm_num)
        · refine Or.inl ?_
          exact (CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_of_M22 e).trans (by norm_num)
        · refine Or.inr ⟨rfl, ?_⟩
          obtain ⟨b⟩ := hON
          exact ⟨e.trans b.symm⟩
        · refine Or.inl ?_
          exact (CFSG.RankThree.PartOne.N143.T2.pRank_three_le_two_of_lie_cover hd e).trans
            (by norm_num)
      · exfalso
        have h4 := hNC Y hq hcat hZ hcyc
        omega
    · have h5 : 5 ≤ p := by
        have h2p : 2 ≤ p := hp.two_le
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
        omega
      exfalso
      have h4 := hC5 Y hq hcat p hp h5 hZ0 hZ
      omega

end CFSG.LocalAnalysis.WeakClosure81.Asch22
