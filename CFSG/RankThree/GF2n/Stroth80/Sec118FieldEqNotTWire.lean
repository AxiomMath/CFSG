module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTClassAll
import CFSG.RankThree.GF2n.Stroth80.Sec118FieldEqNotT

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open scoped Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

section Certificates


theorem Ctx.card_Z_le_two_pow_of_not_cmSpTransvAt [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    (hnT : ¬ CMSpTransvAt M Q Z B m x a h) :
    Nat.card Z ≤ 2 ^ x := by
  refine hc.card_Z_le_two_pow_of_not_transvAt (a := a) (h := h) hw hn hLm ?_
  intro K _ _ _ hK ψ
  obtain ⟨hm3, a₁, c₁, hac, hli, heq⟩ :=
    hc.exists_lineElt_of_not_cmSpTransvAt' hLm ⟨(a : G), h.1, h.2⟩ hnT hK ψ
  refine ⟨hm3, a₁, c₁, hac, hli, fun v => ?_⟩
  have hv := spEquiv_app (ψ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩) v
  rw [heq, lineElt_app spForm_isAlt hac] at hv
  exact hv.symm

end Certificates

end CFSG.RankThree.GF2n.Stroth80
