module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalCorB
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.O2Hbar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem sec93f_listGroup (h44 : Stroth44Statement) (hB : CorollaryBStmt)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {Z0 : Subgroup G}
    (hQZ0 : Q ≤ Z0) (hZ0M : Z0 ≤ M) (hZ0H : Z0 ≤ H0 M Z) (hZ0L : Z0 ≤ LB M Q B)
    (hZ0N : Z0 ≤ hc.CN t)
    (hcentre : ∀ s ∈ Z0, s ∉ Q → ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t)
    (hnQ : ∃ s ∈ Z0, s ∉ Q) (hwc : WeaklyClosedInCent M Q Z0) :
    ListGroup ↥(Subgroup.normalClosure
      (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup ↥(bar M Q (H0 M Z))) :
        Set ↥(bar M Q (H0 M Z)))) := by
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  set T : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hT
  have hCorB : CorBHyp T := sec93f_corBHyp hc hQZ0 hZ0M hZ0H hZ0L hZ0N hcentre hwc
  have hThm : ThmAConclusion T := hB ↥Hb T hCorB
  have hQH : Q ≤ H0 M Z := hQZ0.trans hZ0H
  have hTne : T ≠ ⊥ := by
    obtain ⟨s, hsZ, hsQ⟩ := hnQ
    have hsM : s ∈ M := hZ0M hsZ
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ Hb :=
      (mk_mem_bar_iff_sec4 hQH ⟨s, hsM⟩).mpr (hZ0H hsZ)
    have hmemT : (⟨_, hmem⟩ : ↥Hb) ∈ T := by
      rw [hT, Subgroup.mem_subgroupOf]
      exact (mk_mem_bar_iff_sec4 hQZ0 ⟨s, hsM⟩).mpr hsZ
    intro h
    rw [h, Subgroup.mem_bot] at hmemT
    apply hsQ
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ = 1 := congrArg Subtype.val hmemT
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hTp : IsPGroup 2 T := corB_isPGroup_of_isElemAbelian T hCorB.1
  have hO2 : ∀ P : Subgroup ↥Hb, P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hP hP2
    have hle : P ≤ pCore 2 ↥Hb := le_sSup ⟨hP, hP2⟩
    rw [pCore_two_bar_H0_eq_bot hc] at hle
    exact le_bot_iff.mp hle
  have hΛH : bar M Q (LB M Q B) ≤ Hb := hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0
  have hO : ∀ P : Subgroup ↥Hb, P.Normal → Odd (Nat.card P) → P = ⊥ := by
    intro P hP hPodd
    have hodd : Odd (Nat.card ↥(P.map Hb.subtype)) := by
      rw [← Nat.card_congr (P.equivMapOfInjective Hb.subtype Hb.subtype_injective).toEquiv]
      exact hPodd
    have hbot := h44 G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen (P.map Hb.subtype)
      (Subgroup.map_subtype_le P)
      (fun x hx => sec93f_mem_normalizer_map P (hΛH hx)) hodd
    exact (Subgroup.map_eq_bot_iff_of_injective P Hb.subtype_injective).mp hbot
  exact corB_listGroup hTne hTp hThm hO2 hO

end CFSG.RankThree.GF2n.Stroth80
