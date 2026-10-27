module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveLine
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s23_5_2_of (D : Data G) (Ch : Choice2011 G) (hline : S23_5_line D Ch) (hK : KNshape) :
    S23_5_2 D Ch := by
  intro h1930 c
  rcases hline h1930 c with hL2 | ⟨hLL0, hOm, hL2', -⟩ | ⟨hLL0, hsq, -, -⟩
  · exact Or.inl (hK G c.L0 c.n (CFSG.Open.pRank 2 D.Z) c.hn (Or.inl hL2))
  · exact Or.inr ⟨hLL0, hOm, hK G c.L0 c.n (2 * CFSG.Open.pRank 2 D.Z) c.hn (Or.inl hL2')⟩
  · exact Or.inl (hK G c.L0 c.n (CFSG.Open.pRank 2 D.Z) c.hn (Or.inr hsq))

theorem s23_5_3_of (D : Data G) (Ch : Choice2011 G) (hline : S23_5_line D Ch) (hK : KNshape)
    (hZR : Choice2011ZRepair D Ch) : S23_5_3 D Ch := by
  intro h1930 c hpi
  rcases hline h1930 c with hL2 | ⟨hLL0, hOm, hL2', hpiCB⟩ | ⟨hLL0, hsq, -, -⟩
  · have hcn : c.n = CFSG.Open.pRank 2 D.Z :=
      hK G c.L0 c.n (CFSG.Open.pRank 2 D.Z) c.hn (Or.inl hL2)
    have hZR' := hZR h1930 c hcn
    refine Or.inl (le_bot_iff.mp ?_)
    exact (inf_le_inf_right (Subgroup.centralizer (D.Z : Set G)) c.hle).trans (le_of_eq hZR')
  · have hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z :=
      hK G c.L0 c.n (2 * CFSG.Open.pRank 2 D.Z) c.hn (Or.inl hL2')
    refine Or.inr ⟨hcn, ?_⟩
    ext p
    rw [hpiCB]
    constructor
    · exact fun hp => hp.2
    · intro hp
      refine ⟨?_, hp⟩
      rw [hpi]
      simp only [etaSet, Set.mem_setOf_eq]
      refine ⟨hp.1, ?_⟩
      rw [hcn, CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
      exact dvd_mul_of_dvd_right hp.2 _
  · have hcn : c.n = CFSG.Open.pRank 2 D.Z :=
      hK G c.L0 c.n (CFSG.Open.pRank 2 D.Z) c.hn (Or.inr hsq)
    have hZR' := hZR h1930 c hcn
    refine Or.inl (le_bot_iff.mp ?_)
    exact (inf_le_inf_right (Subgroup.centralizer (D.Z : Set G)) c.hle).trans (le_of_eq hZR')

end CFSG.LocalAnalysis.UniquenessCase.UC22

end