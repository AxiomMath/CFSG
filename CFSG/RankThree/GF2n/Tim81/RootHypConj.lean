module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs
public import CFSG.RankThree.GF2n.ConjTransport
public import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

section HypConj

variable {G : Type} [Group G] {M V : Subgroup G}

theorem Hyp.conjSubgroup (h : Hyp M V) (a : G) :
    Hyp (CGT.Timmesfeld75.conjSubgroup a M) (CGT.Timmesfeld75.conjSubgroup a V) where
  o2 := h.o2
  maxLocal := CFSG.CGT.PushingUp.isMaximalTwoLocal_map_conj h.maxLocal a
  fitting := by
    have e : ↥M ≃* ↥(M.map (MulAut.conj a).toMonoidHom) :=
      MulEquiv.subgroupMap (MulAut.conj a) M
    show generalizedFitting ↥(M.map (MulAut.conj a).toMonoidHom) =
      pCore 2 ↥(M.map (MulAut.conj a).toMonoidHom)
    rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv e, ← CFSG.pCore_map_iso 2 e,
      h.fitting]
  maxAb := CFSG.RankThree.GF2n.maximal_abelianNormal_map_mulEquiv (MulAut.conj a) h.maxAb
  elem := CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup h.elem a
  ti := CFSG.RankThree.GF2n.isTI_conjSubgroup h.ti a

end HypConj

section RootHypConj

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem RootHyp.conjSubgroup (h : RootHyp M V) (a : G) :
    RootHyp (CGT.Timmesfeld75.conjSubgroup a M) (CGT.Timmesfeld75.conjSubgroup a V) where
  toHyp := Hyp.conjSubgroup h.toHyp a
  four_le_card := by
    rw [CFSG.RankThree.GF2n.card_conjSubgroup a V]
    exact h.four_le_card
  weaklyClosed_P := by
    have hwc : WeaklyClosedIn (CGT.Timmesfeld75.conjSubgroup a V)
        (CGT.Timmesfeld75.conjSubgroup a (Pc M V)) :=
      CFSG.RankThree.GF2n.weaklyClosedIn_map_mulEquiv (MulAut.conj a) h.weaklyClosed_P
    rwa [Pc_conjSubgroup]
  rootType := CFSG.RankThree.GF2n.Tim78.isRootTypeTI_conjSubgroup h.rootType a
  not_weaklyClosed := by
    intro hwc
    apply h.not_weaklyClosed
    have h' : WeaklyClosedIn (CGT.Timmesfeld75.conjSubgroup a⁻¹
        (CGT.Timmesfeld75.conjSubgroup a V))
        (CGT.Timmesfeld75.conjSubgroup a⁻¹ (CGT.Timmesfeld75.conjSubgroup a M)) :=
      CFSG.RankThree.GF2n.weaklyClosedIn_map_mulEquiv (MulAut.conj a⁻¹) hwc
    simpa only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      CGT.Timmesfeld75.conjSubgroup_one] using h'

end RootHypConj

section RootHypCen

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

theorem RootHyp.conj_le_centralizer_of_mem_normalizer (hR : RootHyp M V) {a x t : G}
    (ht : t ∈ CGT.Timmesfeld75.conjSubgroup a V) (ht1 : t ≠ 1)
    (htN : t ∈ Subgroup.normalizer (CGT.Timmesfeld75.conjSubgroup x V : Set G)) :
    CGT.Timmesfeld75.conjSubgroup x V ≤
      Subgroup.centralizer (CGT.Timmesfeld75.conjSubgroup a V : Set G) := by
  have hne : CGT.Timmesfeld75.conjSubgroup a V ⊓
      Subgroup.normalizer (CGT.Timmesfeld75.conjSubgroup x V : Set G) ≠ ⊥ := by
    intro hbot
    exact ht1 (Subgroup.mem_bot.mp (hbot.le (Subgroup.mem_inf.mpr ⟨ht, htN⟩)))
  have hc := CFSG.RankThree.GF2n.Tim78.commute_of_isRootTypeTI hR.rootType hne
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a' ha'
  exact hc a' ha' b hb

end RootHypCen

end CFSG.RankThree.GF2n.Tim81

