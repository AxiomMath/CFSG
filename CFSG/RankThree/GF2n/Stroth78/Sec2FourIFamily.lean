module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Stroth78.Sec2Conj

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem isElemAbelian_ZQ (S : Setting z E F) : IsElemAbelian 2 (ZQ z) := by
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  have hzF : z ∈ F := Subgroup.commutator_le_self F S.hyp.mem_derived
  rw [ZQ_eq S]
  refine IsElemAbelian.sup_of_commute S.hyp.elemAbelian (isElemAbelian_zpowers hz2) ?_
  intro e he w hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hk]
  exact ((S.hyp.commute e he z hzF).zpow_right k).eq

theorem isElemAbelian_centerIn_QaOf (S : Setting z E F) {a : G} (hconj : IsConj z a) :
    IsElemAbelian 2 (centerIn (QaOf a)) := by
  obtain ⟨g, hg⟩ := centerIn_QaOf_eq_map S hconj
  rw [hg]
  exact (isElemAbelian_ZQ S).map (MulAut.conj g).toMonoidHom

end CFSG.RankThree.GF2n.Stroth78
