module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.VBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G}

theorem bar_Z0_ne_bot_of_mem_notQ [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : bar M Q Z0 ≠ ⊥ := by
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.toSec5.mem hZ0
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨t, hc.LB_le_M hs.toSec5.mem⟩ ∈ bar M Q Z0 :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htZ0)
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hs.toSec5.notQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem))

theorem bar_Z0_subgroupOf_ne_bot [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≠ ⊥ := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hZbne : bar M Q Z0 ≠ ⊥ := bar_Z0_ne_bot_of_mem_notQ hc hs hZ0
  haveI : Nontrivial ↥(bar M Q Z0) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZbne
  have hlt : 1 < Nat.card ↥(bar M Q Z0) := Finite.one_lt_card
  intro hbot
  have h1 : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hcard : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card ↥(bar M Q Z0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarZ0H).toEquiv
  omega

theorem MbarPrime_eq_normalizer_bar_Z0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    MbarPrime M Q Z Z0 =
      Subgroup.normalizer ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnormR
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) := MbarPrimeLe M Q Z Z0
  have hKnorm : bar M Q (NormH0 M Z Z0) ≤ Subgroup.normalizer (bar M Q Z0) := by
    calc bar M Q (NormH0 M Z Z0)
        = ((NormH0 M Z Z0).subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) := rfl
      _ ≤ ((Subgroup.normalizer (Z0 : Set G)).subgroupOf M).map
            (QuotientGroup.mk' (Q.subgroupOf M)) :=
          Subgroup.map_mono (Subgroup.subgroupOf_mono M inf_le_right)
      _ = (Subgroup.normalizer (Z0.subgroupOf M)).map
            (QuotientGroup.mk' (Q.subgroupOf M)) := by
          rw [Subgroup.subgroupOf_normalizer_eq hZ0M]
      _ ≤ Subgroup.normalizer ((Z0.subgroupOf M).map
            (QuotientGroup.mk' (Q.subgroupOf M))) := Subgroup.le_normalizer_map _
  have hker : (QuotientGroup.mk' (Q.subgroupOf M)).ker ≤ Z0.subgroupOf M := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subgroupOf_mono M hQZ0
  have hcomap : (Subgroup.normalizer (bar M Q Z0)).comap
        (QuotientGroup.mk' (Q.subgroupOf M)) =
      Subgroup.normalizer (Z0.subgroupOf M) := by
    have hmap : bar M Q Z0 = (Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) := rfl
    rw [hmap, Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      Subgroup.comap_map_eq_self hker]
  have hNorm : (NormH0 M Z Z0).subgroupOf M =
      (H0 M Z).subgroupOf M ⊓ (Subgroup.normalizer (Z0 : Set G)).subgroupOf M := by
    ext x
    simp [NormH0, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hK : bar M Q (NormH0 M Z Z0) =
      bar M Q (H0 M Z) ⊓ Subgroup.normalizer (bar M Q Z0) := by
    refine le_antisymm (le_inf hKH hKnorm) ?_
    rintro y ⟨hyH, hyn⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hyH
    refine Subgroup.mem_map_of_mem _ ?_
    rw [hNorm]
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    have h1 : x ∈ (Subgroup.normalizer (bar M Q Z0)).comap
        (QuotientGroup.mk' (Q.subgroupOf M)) := hyn
    rw [hcomap] at h1
    rwa [Subgroup.subgroupOf_normalizer_eq hZ0M]
  show (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)) =
    Subgroup.normalizer ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
  rw [hK, Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hbarZ0H]

theorem isTwoLocal_MbarPrime [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZc : Sec7CentreStatement) :
    CFSG.Open.IsTwoLocal (MbarPrime M Q Z Z0) := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hE : Assembly.IsElemAbelian 2 (bar M Q Z0) := isElemAbelian_bar_Z0 hc hs hZc hZ0
  have hP2 : IsPGroup 2 ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) :=
    (CFSG.Open.IsElemAbelian.isPGroup hE).of_equiv (Subgroup.subgroupOfEquivOfLe hbarZ0H).symm
  exact ⟨_, bar_Z0_subgroupOf_ne_bot hc hs hZ0, hP2,
    MbarPrime_eq_normalizer_bar_Z0 hc hs hZ0⟩

theorem generalizedFitting_MbarPrime [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (h712 : Stroth712Statement) :
    generalizedFitting (MbarPrime M Q Z Z0) = pCore 2 (MbarPrime M Q Z Z0) := by
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) := MbarPrimeLe M Q Z Z0
  let e : ↥(MbarPrime M Q Z Z0) ≃* ↥(bar M Q (NormH0 M Z Z0)) :=
    Subgroup.subgroupOfEquivOfLe hKH
  have hmapF : (generalizedFitting (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have hmapP : (pCore 2 (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      pCore 2 ↥(bar M Q (NormH0 M Z Z0)) :=
    CFSG.pCore_map_iso 2 e
  have h712' : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      pCore 2 ↥(bar M Q (NormH0 M Z Z0)) := h712 G M Q Z B hc n t hs Z0 hZ0
  exact Subgroup.map_injective e.injective (hmapF.trans (h712'.trans hmapP.symm))

theorem generalizedFitting_MbarPrime_eq_CN [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h713 : Stroth713Statement) (hn4 : ¬ OmegaPlusNat hc t 4) :
    generalizedFitting (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) := by
  have hCNN : hc.CN t ≤ NormH0 M Z Z0 := fun x hx =>
    sec8_Rt_le_NormH0 hc hZ0 (Ctx.mem_CN.mp hx).1
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) := MbarPrimeLe M Q Z Z0
  let e : ↥(MbarPrime M Q Z Z0) ≃* ↥(bar M Q (NormH0 M Z Z0)) :=
    Subgroup.subgroupOfEquivOfLe hKH
  have hmapF : (generalizedFitting (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) :=
    CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  have h713' : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) :=
    h713 G M Q Z B hc n t hs hn4 Z0 hZ0
  have hmapS : (((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0)).map e.toMonoidHom =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨⟨y.1, hKH y.2⟩, y.2⟩, hy, rfl⟩
  exact Subgroup.map_injective e.injective (hmapF.trans (h713'.trans hmapS.symm))

theorem pCore_two_MbarPrime_eq_CN [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h712 : Stroth712Statement) (h713 : Stroth713Statement) (hn4 : ¬ OmegaPlusNat hc t 4) :
    pCore 2 (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) := by
  rw [← generalizedFitting_MbarPrime hc hs hZ0 h712]
  exact generalizedFitting_MbarPrime_eq_CN hc hs hZ0 h713 hn4
