module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.MaxAbCentralizer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.M_le_normalizer_commXbarPre (hc : Ctx M Q Z B) :
    M ≤ Subgroup.normalizer ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff]
  have h1 : conjSubgroup m ⁅Q, XbarPre M Q Z B⁆ =
      ⁅conjSubgroup m Q, conjSubgroup m (XbarPre M Q Z B)⁆ := by
    unfold conjSubgroup
    exact Subgroup.map_commutator _ _ _
  rw [h1, hc.conj_Q_eq hm, XbarPre_normal hc hm]

theorem Ctx.commXbarPre_sup_inf_centralizer_eq (hc : Ctx M Q Z B) :
    (⁅Q, XbarPre M Q Z B⁆ ⊔ Z) ⊓
      Subgroup.centralizer ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) = Z :=
  hc.hyp.sup_inf_centralizer_eq (commutator_le_Q hc) hc.M_le_normalizer_commXbarPre

end CFSG.RankThree.GF2n.Stroth80
