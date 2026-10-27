module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117F4Producer
import CFSG.RankThree.GF2n.Stroth80.HeringSec117F4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.not_lieModel_F4_xbarMod [Finite G]
    [(Q.subgroupOf M).Normal]
    (hF1 : F4ExclStatement) (hF2 : F4GenStatement)
    (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {m x : ℕ} :
    ¬ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .F4 m 2 x := by
  intro hX
  obtain ⟨-, -, rfl⟩ := hX.admissible
  exact hc.not_lieModel_f4_of hF1 hF2 ha2 hX

end CFSG.RankThree.GF2n.Stroth80
