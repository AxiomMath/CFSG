module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110StatementCase
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCase

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem stroth1110_of_inputs [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (h3 : CMLmThree)
    (hLgen : ∀ (m x : ℕ), 4 ≤ m →
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x →
      Lgen M (LB M Q B) ≤ XbarPre M Q Z B)
    (hL : IsLmChar2 (XbarMod M Q Z B)) :
    Xbar M Q Z B = bar M Q (Lgen M (LB M Q B)) ∧
      CaseVICore M Q Z (Lgen M (LB M Q B)) n := by
  rcases isLmChar2_cases hL with ⟨x, h2⟩ | ⟨m, x, hm, hLm⟩
  · exact stroth1110_of_lieModel_psl_two hc hw hn ⟨x, h2⟩
  · exact stroth1110_of_inputs_m_ge_three hc hw hn ha2 hC h3 ⟨m, x, hm, hLm⟩ hLgen

end CFSG.RankThree.GF2n.Stroth80
