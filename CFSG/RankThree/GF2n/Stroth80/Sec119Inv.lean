module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.ClassicalGroups.Orthogonal.RootInvolutionRadical
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec116Elt
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.dvd_of_card_Z_eq_two_pow_of_omega (hc : Ctx M Q Z B) {n m x a : ℕ}
    (hw : Width Q Z n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hΩ : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaPlus m 2 x ∨
      CFSG.Blueprint.LieModel (XbarMod M Q Z B) .POmegaMinus m 2 x ∨
      (m = 3 ∧ CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x))
    (ha : Nat.card Z = 2 ^ a) : x ∣ a := by
  have hx : 1 ≤ x := by
    rcases hΩ with h | h | ⟨-, h⟩
    · exact h.admissible.2.1
    · exact h.admissible.2.1
    · exact h.admissible.2.1
  obtain ⟨d₀, hd₀⟩ := hc.Ebar_nonempty ha2
  let t : ↥(Xbar M Q Z B) := ⟨d₀, Subgroup.subset_closure hd₀⟩
  have ht : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact Ctx.orderOf_eq_two_of_mem_Ebar hd₀
  have ht' := CFSG.RankThree.OddKernel.orderOf_mk_eq_two (Subgroup.center ↥(Xbar M Q Z B))
    hc.odd_card_center_Xbar ht
  obtain ⟨g, hgo, hg⟩ := CFSG.ClassicalGroups.Orthogonal.exists_inv_conj_of_lieModel_omega hΩ ht'
    (hc.orderOf_mul_conj_mk_of_mem_Ebar (t := t) hd₀)
  exact hc.dvd_of_inv_conj_mk_of_mem_Ebar hw hx (t := t) hd₀ hgo hg ha

end CFSG.RankThree.GF2n.Stroth80
