module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MPrime
public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar
public import CFSG.RankThree.GF2n.Tim81.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Tim81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem not_weaklyClosed_bar_Z0 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZc : Sec7CentreStatement)
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0) :
    ¬ WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (MbarPrime M Q Z Z0) := by
  intro hwc
  apply hNL
  intro x hx
  obtain ⟨hxH0, hxNL⟩ := hx
  have hxM : x ∈ M := hxH0.1
  let xM : M := ⟨x, hxM⟩
  let xH : Hbar M Q Z := ⟨QuotientGroup.mk' (Q.subgroupOf M) xM,
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxH0)⟩
  have hLBH : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M (fun y hy => hc.LB_le_H0 hy))
  have hxbarNL : (xH : Mbar M Q) ∈ bar M Q (NormH0L M Z (LB M Q B)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hxH0, hxNL⟩)
  have hnormMbar : (xH : Mbar M Q) ∈
      Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)) :=
    (bar_le_normalizer_of_le_normalizer (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M
      (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
        from hy).1.1)
      (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
        from hy).2) hxbarNL)
  have hLbar_norm : xH ∈ Subgroup.normalizer
      ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) : Set (Hbar M Q Z)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hLBH]
    exact Subgroup.mem_subgroupOf.mpr hnormMbar
  have hZ0LB : Z0 ≤ LB M Q B := fun z hz =>
    ((hZc G M Q Z B hc n t hs Z0 hZ0 z).mp hz).1
  have hVL : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.subgroupOf_mono _ (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0LB))
  have hconj_le : conjSubgroup xH ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ≤
      (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
    calc conjSubgroup xH ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
        ≤ conjSubgroup xH ((bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))) :=
          Subgroup.map_mono hVL
      _ = (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) := by
          rw [conjSubgroup_eq_self_iff]
          exact hLbar_norm
  have hLBnorm : LB M Q B ≤ NormH0 M Z Z0 := by
    intro y hy
    have hyR : y ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) hs.toSec5.mem hy
    have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q :=
      fun r hr y hy => (Subgroup.mem_normalizer_iff.mp
        (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
    exact Subgroup.mem_inf.mpr ⟨hc.LB_le_H0 hy,
      IsCentrePre.mem_normalizer hZ0 hnormR hyR⟩
  have hLbarM : (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z)) ≤
      MbarPrime M Q Z Z0 :=
    Subgroup.subgroupOf_mono _ (Subgroup.map_mono
      (f := QuotientGroup.mk' (Q.subgroupOf M)) (Subgroup.subgroupOf_mono M hLBnorm))
  have hconjM : conjSubgroup xH ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ≤
      MbarPrime M Q Z Z0 := hconj_le.trans hLbarM
  have heq : conjSubgroup xH ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := hwc.2 xH hconjM
  have hxN : xH ∈ Subgroup.normalizer
      ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Set (Hbar M Q Z)) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr heq
  have hxM' : xH ∈ MbarPrime M Q Z Z0 := by
    rw [MbarPrime_eq_normalizer_bar_Z0 hc hs hZ0]
    exact hxN
  have hxbarNorm : (xH : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_subgroupOf.mp hxM'
  have hQZ0 : Q ≤ Z0 := by
    have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q :=
      fun r hr y hy => (Subgroup.mem_normalizer_iff.mp
        (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
    exact IsCentrePre.Q_le hZ0 (hc.Q_le_Rt hs.toSec5.mem) hnormR
  have hQH : Q ≤ H0 M Z := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hc.hyp.Q_normal.1 hq,
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [hc.hyp.hZ, cen_eq] at hz
        exact (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm⟩
  have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
    Subgroup.mem_inf.mpr ⟨hQH hq, Z0.le_normalizer (hQZ0 hq)⟩
  exact (mk_mem_bar_iff_sec4 hQN xM).mp hxbarNorm

theorem exists_isHMember (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h34 : Stroth34Statement) (h712 : Stroth712Statement) (h713 : Stroth713Statement)
    (hn4 : ¬ OmegaPlusNat hc t 4)
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0) :
    ∃ H : Subgroup (Hbar M Q Z),
      IsHMember (MbarPrime M Q Z Z0)
        ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) H := by
  have h5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  let Hw : Subgroup (Hbar M Q Z) :=
    (bar M Q (NormH0L M Z (LB M Q B))).subgroupOf (bar M Q (H0 M Z))
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hCNN : hc.CN t ≤ Subgroup.normalizer (LB M Q B : Set G) := by
    intro y hy
    have h := hc.CN_normalizes_conj_LB h35 hs.toSec5.mem (h := 1) (Subgroup.one_mem _) hy
    rwa [conjSubgroup_one_sec4] at h
  have hCNL : bar M Q (hc.CN t) ≤ bar M Q (NormH0L M Z (LB M Q B)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M (fun y hy =>
      Subgroup.mem_inf.mpr ⟨hCNH0 hy, hCNN hy⟩))
  have hPc : Pc (MbarPrime M Q Z Z0) V ≤ Hw := by
    refine (inf_le_left.trans ?_)
    have hpc := pCore_two_MbarPrime_eq_CN hc hs hZ0 h712 h713 hn4
    change (pCore 2 (MbarPrime M Q Z Z0)).map (MbarPrime M Q Z Z0).subtype ≤ Hw
    rw [hpc, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans (Subgroup.subgroupOf_mono _ hCNL)
  have hO2 : inSubgroup (pCore 2) Hw ≠ ⊥ := by
    let L : Subgroup (Hbar M Q Z) :=
      (bar M Q (LB M Q B)).subgroupOf (bar M Q (H0 M Z))
    have hLH : L ≤ Hw := by
      apply Subgroup.subgroupOf_mono
      exact Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M (fun y hy => Subgroup.mem_inf.mpr
          ⟨hc.LB_le_H0 hy, Subgroup.le_normalizer hy⟩))
    have hLHbar : bar M Q (LB M Q B) ≤ bar M Q (H0 M Z) :=
      Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
        (Subgroup.subgroupOf_mono M (fun y hy => hc.LB_le_H0 hy))
    have hLnormH : Hw ≤ Subgroup.normalizer (L : Set (Hbar M Q Z)) := by
      have hN := bar_le_normalizer_of_le_normalizer (le_sup_left : Q ≤ LB M Q B)
        hc.LB_le_M
        (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
          from hy).1.1)
        (fun y hy => (show y ∈ H0 M Z ⊓ Subgroup.normalizer (LB M Q B : Set G)
          from hy).2)
      intro x hx
      have hxbar : (x : Mbar M Q) ∈ bar M Q (NormH0L M Z (LB M Q B)) :=
        Subgroup.mem_subgroupOf.mp hx
      rw [← Subgroup.subgroupOf_normalizer_eq hLHbar]
      exact Subgroup.mem_subgroupOf.mpr (hN hxbar)
    have hLnormal : (L.subgroupOf Hw).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hLnormH
    have hLp : IsPGroup 2 (L.subgroupOf Hw) := by
      have hE : Assembly.IsElemAbelian 2 (bar M Q (LB M Q B)) := hc.isElemAbelian_bar_LB
      have hP : IsPGroup 2 (bar M Q (LB M Q B)) := CFSG.Open.IsElemAbelian.isPGroup hE
      have hPL : IsPGroup 2 L :=
        hP.of_equiv (Subgroup.subgroupOfEquivOfLe hLHbar).symm
      exact hPL.of_equiv (Subgroup.subgroupOfEquivOfLe hLH).symm
    have hLne_sub : L.subgroupOf Hw ≠ ⊥ := by
      intro hbot
      have hLbot : L = ⊥ := by
        have := congrArg (Subgroup.map Hw.subtype) hbot
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLH,
          Subgroup.map_bot] at this
      have hcard : 4 ≤ Nat.card L := by
        have hbar := hc.four_le_card_bar_LB h34 h5.width h5.n_gt h5.noA2 h5.gen
        rw [show Nat.card L = Nat.card (bar M Q (LB M Q B)) by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLHbar).toEquiv]
        exact hbar
      rw [hLbot, Subgroup.card_bot] at hcard
      omega
    have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (p := 2)
      hLnormal hLp
    intro hbot
    have hLbot : L.subgroupOf Hw = ⊥ := by
      have hbot' : Subgroup.map Hw.subtype (pCore 2 ↥Hw) = ⊥ := hbot
      have hmap := Subgroup.map_mono (f := Hw.subtype) hle
      rw [hbot'] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective (L.subgroupOf Hw)
        (f := Hw.subtype) Hw.subtype_injective).mp (le_bot_iff.mp hmap)
    exact hLne_sub hLbot
  have hnotle : ¬ Hw ≤ MbarPrime M Q Z Z0 := by
    intro hle
    apply hNL
    intro x hx
    obtain ⟨hxH0, hxNL⟩ := hx
    have hxM : x ∈ M := hxH0.1
    let xM : M := ⟨x, hxM⟩
    let xH : Hbar M Q Z := ⟨QuotientGroup.mk' (Q.subgroupOf M) xM,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxH0)⟩
    have hxHw : xH ∈ Hw := Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hxH0, hxNL⟩))
    have hxM' : xH ∈ MbarPrime M Q Z Z0 := hle hxHw
    have hxbarNorm : (xH : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
      Subgroup.mem_subgroupOf.mp hxM'
    have hQZ0 : Q ≤ Z0 := by
      have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q :=
        fun r hr y hy => (Subgroup.mem_normalizer_iff.mp
          (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
      exact IsCentrePre.Q_le hZ0 (hc.Q_le_Rt hs.toSec5.mem) hnormR
    have hQH : Q ≤ H0 M Z := fun q hq =>
      Subgroup.mem_inf.mpr ⟨hc.hyp.Q_normal.1 hq,
        Subgroup.mem_centralizer_iff.mpr fun z hz => by
          rw [hc.hyp.hZ, cen_eq] at hz
          exact (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm⟩
    have hQN : Q ≤ NormH0 M Z Z0 := fun q hq =>
      Subgroup.mem_inf.mpr ⟨hQH hq, Z0.le_normalizer (hQZ0 hq)⟩
    exact (mk_mem_bar_iff_sec4 hQN xM).mp hxbarNorm
  exact ⟨Hw, hO2, hPc, hnotle⟩

end CFSG.RankThree.GF2n.Stroth80
