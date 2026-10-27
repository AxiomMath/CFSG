module

public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalList
public import CFSG.RankThree.GF2n.Stroth80.Sec93FinalStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem close93FinalWithClaimThree_of_bound (hbound : ListWCBoundStatement) (hB : CorollaryBStmt)
    (h44 : Stroth44Statement) (h34 : Stroth34Statement) (hn5 : Sec9NGeFiveStatement)
    (hC : Step95CentreStatement) : Close93FinalWithClaimThreeStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 he3 hwc
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hs5 : Sec5Hyp hc n t := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZ0H : Z0 ≤ H0 M Z := hZ0.le.trans (hc.Rt_le_H0 t)
  obtain ⟨hZ0LN, hrel, hcentre⟩ := hC G M Q Z B hc n t hs Z0 hZ0
  have hZ0L : Z0 ≤ LB M Q B := fun x hx => (hZ0LN hx).1
  have hZ0N : Z0 ≤ hc.CN t := fun x hx => (hZ0LN hx).2
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hnQ : ∃ s ∈ Z0, s ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hle : Z0 ≤ Q := fun x hx => hcon x hx
    have h1 : Q.relIndex Z0 = 1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  set Hb : Subgroup (Mbar M Q) := bar M Q (H0 M Z) with hHb
  set T : Subgroup ↥Hb := (bar M Q Z0).subgroupOf Hb with hT
  set L : Subgroup ↥Hb := (bar M Q (LB M Q B)).subgroupOf Hb with hL
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hLBM : LB M Q B ≤ M := hc.LB_le_M
  have hQH : Q ≤ H0 M Z := hQZ0.trans hZ0H
  have hbarZH : bar M Q Z0 ≤ Hb :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hZ0H (Subgroup.mem_subgroupOf.mp hx))
  have hbarZL : bar M Q Z0 ≤ bar M Q (LB M Q B) :=
    Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hZ0L (Subgroup.mem_subgroupOf.mp hx))
  have hΛH : bar M Q (LB M Q B) ≤ Hb :=
    hc.bar_LB_le_bar_Lgen.trans hc.bar_Lgen_le_bar_H0
  have hTL : T ≤ L := fun x hx => Subgroup.mem_subgroupOf.mpr
    (hbarZL (Subgroup.mem_subgroupOf.mp hx))
  have hCorB : CorBHyp T := sec93f_corBHyp hc hQZ0 hZ0M hZ0H hZ0L hZ0N hcentre hwc
  have hList := sec93f_listGroup h44 hB hc hs5 hQZ0 hZ0M hZ0H hZ0L hZ0N hcentre hnQ hwc
  have hLBel := hc.isElemAbelian_bar_LB
  have hLel : IsElemAbelian 2 L := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : (a.1 : Mbar M Q) ∈ bar M Q (LB M Q B) := Subgroup.mem_subgroupOf.mp a.2
      have hb : (b.1 : Mbar M Q) ∈ bar M Q (LB M Q B) := Subgroup.mem_subgroupOf.mp b.2
      have h := congrArg Subtype.val (hLBel.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
      exact Subtype.ext (Subtype.ext h)
    · have hx' : (x : Mbar M Q) ∈ bar M Q (LB M Q B) := Subgroup.mem_subgroupOf.mp hx
      have h2 := hLBel.2 (x : Mbar M Q) hx'
      exact Subtype.ext (by simpa using h2)
  have lift : ∀ g : ↥Hb, ∃ m : M, QuotientGroup.mk' (Q.subgroupOf M) m = (g : Mbar M Q) := by
    intro g
    obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp g.2
    exact ⟨y, hy⟩
  have memT : ∀ (x : ↥Hb) (w : M), (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) w →
      (x ∈ T ↔ (w : G) ∈ Z0) := by
    intro x w hxw
    rw [hT, Subgroup.mem_subgroupOf, hxw]
    exact mk_mem_bar_iff_sec4 hQZ0 w
  have memL : ∀ (x : ↥Hb) (w : M), (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) w →
      (x ∈ L ↔ (w : G) ∈ LB M Q B) := by
    intro x w hxw
    rw [hL, Subgroup.mem_subgroupOf, hxw]
    exact mk_mem_bar_iff_sec4 hQLB w
  have hqpos : 0 < Nat.card Q := Nat.card_pos
  have hTcard : Nat.card T = Nat.card Z := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarZH).toEquiv]
    have h1 := bar_card_mul_card_of_le (M := M) hQZ0 hZ0M
    have h2 := Subgroup.relIndex_mul_card (H := Q) (K := Z0)
    rw [inf_eq_left.mpr hQZ0, hrel] at h2
    exact Nat.eq_of_mul_eq_mul_right hqpos (h1.trans h2.symm)
  have hLcard : Nat.card L = Nat.card Z ^ (n - 1) := by
    rw [hL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛH).toEquiv]
    have h1 := bar_card_mul_card_of_le (M := M) hQLB hLBM
    have h2 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
    exact Nat.eq_of_mul_eq_mul_right hqpos (h1.trans (h2.trans (mul_comm _ _)))
  have hTne : T ≠ ⊥ := by
    obtain ⟨s, hsZ, hsQ⟩ := hnQ
    have hsM : s ∈ M := hZ0M hsZ
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ Hb :=
      (mk_mem_bar_iff_sec4 hQH ⟨s, hsM⟩).mpr (hZ0H hsZ)
    have hmemT : (⟨_, hmem⟩ : ↥Hb) ∈ T := (memT _ ⟨s, hsM⟩ rfl).mpr hsZ
    intro h
    rw [h, Subgroup.mem_bot] at hmemT
    apply hsQ
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ = 1 := congrArg Subtype.val hmemT
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hclaim : ∀ h : ↥Hb, L ⊓ conjSubgroup h L ≠ ⊥ → T ⊓ conjSubgroup h L ≠ ⊥ := by
    intro g hne
    obtain ⟨m, hm⟩ := lift g
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hyL, hyg⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨w, hw⟩ := lift y
    have hwL : (w : G) ∈ LB M Q B := (memL y w hw.symm).mp hyL
    have hyg' : g⁻¹ * y * g ∈ L := mem_conjSubgroup.mp hyg
    have key : ((g⁻¹ * y * g : ↥Hb) : Mbar M Q) =
        QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * w * m) := by
      rw [map_mul, map_mul, map_inv, hm, hw]
      rfl
    have hmwm : ((m⁻¹ * w * m : M) : G) ∈ LB M Q B := (memL _ _ key).mp hyg'
    have hwQ : (w : G) ∉ Q := by
      intro hwQ
      apply hy1
      have h1 : QuotientGroup.mk' (Q.subgroupOf M) w = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwQ)
      refine Subtype.ext (Subtype.ext ?_)
      show (y : Mbar M Q) = 1
      rw [← hw]
      exact h1
    have hwconj : (w : G) ∈ conjSubgroup (m : G) (LB M Q B) :=
      mem_conjSubgroup.mpr (by simpa using hmwm)
    have hne3 : LB M Q B ⊓ conjSubgroup (m : G) (LB M Q B) ≠ Q := by
      intro h
      apply hwQ
      rw [← h]
      exact ⟨hwL, hwconj⟩
    have h3 := he3 (m : G) m.2 hne3
    have hex : ∃ z ∈ Z0 ⊓ (LB M Q B ⊓ conjSubgroup (m : G) (LB M Q B)), z ∉ Q := by
      by_contra hcon
      push Not at hcon
      apply h3
      refine le_antisymm (fun z hz => hcon z hz) (fun z hz => ?_)
      have hzm : (m : G)⁻¹ * z * m ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem m.2)) z).mp hz
        simpa using this
      exact ⟨hQZ0 hz, hQLB hz, mem_conjSubgroup.mpr (hQLB hzm)⟩
    obtain ⟨z, hz, hzQ⟩ := hex
    obtain ⟨hzZ0, hzL, hzc⟩ := (Subgroup.mem_inf.mp hz).imp id Subgroup.mem_inf.mp
    have hzM : z ∈ M := hZ0M hzZ0
    have hzH : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ Hb :=
      (mk_mem_bar_iff_sec4 hQH ⟨z, hzM⟩).mpr (hZ0H hzZ0)
    set zb : ↥Hb := ⟨_, hzH⟩ with hzb
    have hzT : zb ∈ T := (memT zb ⟨z, hzM⟩ rfl).mpr hzZ0
    have hzconj : zb ∈ conjSubgroup g L := by
      refine mem_conjSubgroup.mpr ?_
      have key2 : ((g⁻¹ * zb * g : ↥Hb) : Mbar M Q) =
          QuotientGroup.mk' (Q.subgroupOf M) (m⁻¹ * ⟨z, hzM⟩ * m) := by
        rw [map_mul, map_mul, map_inv, hm]
        rfl
      refine (memL _ _ key2).mpr ?_
      have := mem_conjSubgroup.mp hzc
      simpa using this
    have hz1 : zb ≠ 1 := by
      intro h
      apply hzQ
      have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ = 1 := congrArg Subtype.val h
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    intro hbot
    have : zb ∈ T ⊓ conjSubgroup g L := Subgroup.mem_inf.mpr ⟨hzT, hzconj⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 this
  have hbd := hbound ↥Hb T L hTne hTL hLel hCorB hList hclaim
  rw [hTcard, hLcard] at hbd
  have hn5' := hn5 G M Q Z B hc n t hs
  have h4 : Nat.card Z ^ 4 ≤ Nat.card Z ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end CFSG.RankThree.GF2n.Stroth80
