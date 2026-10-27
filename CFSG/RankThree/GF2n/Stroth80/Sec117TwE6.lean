module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6KLConfig
import CFSG.RankThree.GF2n.Stroth80.Sec117KProducer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.not_lieModel_twistedE6_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .twistedE6 m 2 x := by
  intro h
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  obtain ⟨t, N, A, -, hKL, -⟩ := hc.exists_isKLConfig hw hn ha2 ha
  exact false_of_isKLConfig_of_lieModel_twistedE6 h hKL

end CFSG.RankThree.GF2n.Stroth80
