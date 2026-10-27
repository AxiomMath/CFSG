module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110FieldEq

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.exists_psl4_of_lieModel (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 4 2 x) :
    ∃ y : ℕ, 2 ^ y = Nat.card Z ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 4 2 y :=
  ⟨x, hc.two_pow_eq_card_Z_of_psl hw ha2 h (by norm_num), h⟩

end CFSG.RankThree.GF2n.Stroth80
