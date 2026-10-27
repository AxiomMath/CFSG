module

public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Main
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.TI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem isCentrePre_le_H0_sp (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ H0 M Z :=
  (IsCentrePre.le hZ0).trans (hc.Rt_le_H0 t)

theorem isElemAbelian_bar_Z0_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Assembly.IsElemAbelian 2 (bar M Q Z0) := by
  have hZL : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
  exact hc.isElemAbelian_bar_LB.mono
    (Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZL))

theorem isElemAbelian_bar_Z0_subgroupOf_sp (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Assembly.IsElemAbelian 2
      ((VbarPrime M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup (Hbar M Q Z)) :=
  (isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0).subgroupOf (bar M Q (H0 M Z))

theorem card_bar_Z0_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Nat.card ↥(bar M Q Z0) = Nat.card Z := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnorm
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hcard := bar_card_mul_card_of_le (M := M) (S := Z0) hQZ0 hZ0M
  have hZ0card := sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  rw [hZ0card, Nat.mul_comm (Nat.card Q) (Nat.card Z)] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard

theorem four_le_card_bar_Z0_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    4 ≤ Nat.card ↥(bar M Q Z0) := by
  rw [card_bar_Z0_sp h51 hA hc hs hZ0]
  exact hc.hyp.q4

theorem bar_Z0_ne_bot_of_mem_notQ_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : bar M Q Z0 ≠ ⊥ := by
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.toSec5.mem hZ0
  have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨t, hc.LB_le_M hs.toSec5.mem⟩ ∈ bar M Q Z0 :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htZ0)
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hs.toSec5.notQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem))

theorem bar_Z0_subgroupOf_ne_bot_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≠ ⊥ := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hZbne : bar M Q Z0 ≠ ⊥ := bar_Z0_ne_bot_of_mem_notQ_sp hc hs hZ0
  haveI : Nontrivial ↥(bar M Q Z0) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZbne
  have hlt : 1 < Nat.card ↥(bar M Q Z0) := Finite.one_lt_card
  intro hbot
  have h1 : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hcard : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card ↥(bar M Q Z0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarZ0H).toEquiv
  omega

theorem MbarPrime_eq_normalizer_bar_Z0_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    MbarPrime M Q Z Z0 =
      Subgroup.normalizer ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnormR
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
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
    rw [Subgroup.subgroupOf_normalizer_eq hZ0M]
    exact h1
  show (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)) =
    Subgroup.normalizer ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
  rw [hK, Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hbarZ0H]

theorem isTwoLocal_MbarPrime_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    CFSG.Open.IsTwoLocal (MbarPrime M Q Z Z0) := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hE : Assembly.IsElemAbelian 2 (bar M Q Z0) := isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0
  have hP2 : IsPGroup 2 ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) :=
    (CFSG.Open.IsElemAbelian.isPGroup hE).of_equiv (Subgroup.subgroupOfEquivOfLe hbarZ0H).symm
  exact ⟨_, bar_Z0_subgroupOf_ne_bot_sp hc hs hZ0, hP2,
    MbarPrime_eq_normalizer_bar_Z0_sp hc hs hZ0⟩

theorem generalizedFitting_MbarPrime_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hF2 : Step85F2Statement) :
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
  have hF2' : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      pCore 2 ↥(bar M Q (NormH0 M Z Z0)) := hF2 G M Q Z B hc n t hs Z0 hZ0
  exact Subgroup.map_injective e.injective (hmapF.trans (hF2'.trans hmapP.symm))

theorem isTI_bar_Z0_mbar_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hN : ElementwiseNormalizerHyp M Q Z0) :
    IsTI (VbarPrime M Q Z0) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnormR
  intro g
  by_cases hdis : VbarPrime M Q Z0 ⊓ conjSubgroup g (VbarPrime M Q Z0) = ⊥
  · exact Or.inl hdis
  · right
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hdis
    have hxne : (x : Mbar M Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2.1
    have hyZ0 : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hy
    have hyQ : (y : G) ∉ Q := fun h =>
      hxne (by
        rw [← hyx]
        exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr h))
    have hxc : QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q Z0) := by
      rw [hyx]; exact x.2.2
    have hyconj : (y : G) ∈ conjSubgroup (m : G) Z0 :=
      (mk_mem_conj_bar_iff_sec4 hQZ0 m y).mp hxc
    have huZ0 : (m : G)⁻¹ * (y : G) * (m : G) ∈ Z0 := by
      simpa [mem_conjSubgroup] using hyconj
    have huQ : (m : G)⁻¹ * (y : G) * (m : G) ∉ Q := by
      intro h
      have hyq : (y : G) ∈ Q := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) _).mp h
        have e : (m : G) * ((m : G)⁻¹ * (y : G) * (m : G)) * (m : G)⁻¹ = (y : G) := by
          group
        rw [← e]
        exact h2
      exact hyQ hyq
    have hmN : (m : G) ∈ Subgroup.normalizer (Z0 : Set G) := by
      refine hN (m : G) m.2 ((m : G)⁻¹ * (y : G) * (m : G)) huZ0 huQ ?_
      have e : (m : G) * ((m : G)⁻¹ * (y : G) * (m : G)) * (m : G)⁻¹ = (y : G) := by
        group
      rw [e]
      exact hyZ0
    have hmconjG : conjSubgroup (m : G) Z0 = Z0 := conjSubgroup_eq_self_iff.mpr hmN
    have hsub : conjSubgroup (⟨m, m.2⟩ : ↥M) (Z0.subgroupOf M) = Z0.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [← CFSG.GroupTheory.map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le
        ((IsCentrePre.le hZ0).trans (hc.Rt_le_M t))]
      simpa using hmconjG
    have hmbar : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q Z0) =
        bar M Q Z0 := by
      change conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨m, m.2⟩)
        ((Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) =
        (Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))
      rw [CFSG.GroupTheory.map_conjSubgroup, hsub]
    rw [hmbar, inf_idem]

theorem isTI_bar_Z0_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hN : ElementwiseNormalizerHyp M Q Z0) :
    IsTI ((VbarPrime M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup (Hbar M Q Z)) :=
  (isTI_bar_Z0_mbar_sp hc hs hZ0 hN).subgroupOf (bar M Q (H0 M Z))

theorem not_weaklyClosed_bar_Z0_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
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
  have hZ0LB : Z0 ≤ LB M Q B := sec8_Z0_le_LB h51 hA hc hs hZ0
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
    rw [MbarPrime_eq_normalizer_bar_Z0_sp hc hs hZ0]
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

theorem exists_conj_le_CN_of_pCore_le_of_not_weaklyClosed_sp
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hVleO2 : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      inSubgroup (pCore 2) (MbarPrime M Q Z Z0))
    (hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    (hNWC : ¬ WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 := by
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt hs.toSec5.mem
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hx : ∃ x : Hbar M Q Z, conjSubgroup x V ≤ inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ∧
      conjSubgroup x V ≠ V := by
    by_contra hcon
    apply hNWC
    refine ⟨hVleO2, fun x hxle => ?_⟩
    by_contra hne
    exact hcon ⟨x, hxle, hne⟩
  obtain ⟨x, hxle, hxne⟩ := hx
  obtain ⟨y, hyH0, hyx⟩ := Subgroup.mem_map.mp x.2
  let g : G := y.1
  have hgM : g ∈ M := y.2
  have hgH0 : g ∈ H0 M Z := Subgroup.mem_subgroupOf.mp hyH0
  have hy_eq : (x : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) y := hyx.symm
  have hconjH : conjSubgroup g Z0 ≤ H0 M Z := by
    rintro w ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem hgM (hZ0M hz)) (M.inv_mem hgM), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hgu : u * g = g * u := Subgroup.mem_centralizer_iff.mp hgH0.2 u hu
    have hzu : u * z = z * u := Subgroup.mem_centralizer_iff.mp (hZ0H hz).2 u hu
    have hgu' : u * g⁻¹ = g⁻¹ * u := by
      calc u * g⁻¹ = g⁻¹ * (g * u) * g⁻¹ := by group
        _ = g⁻¹ * (u * g) * g⁻¹ := by rw [hgu]
        _ = g⁻¹ * u := by group
    calc u * (g * z * g⁻¹) = (u * g) * z * g⁻¹ := by group
      _ = (g * u) * z * g⁻¹ := by rw [hgu]
      _ = g * (u * z) * g⁻¹ := by group
      _ = g * (z * u) * g⁻¹ := by rw [hzu]
      _ = g * z * (u * g⁻¹) := by group
      _ = g * z * (g⁻¹ * u) := by rw [hgu']
      _ = (g * z * g⁻¹) * u := by group
  have hbarconjH : bar M Q (conjSubgroup g Z0) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hconjH)
  have hconjBar : bar M Q (conjSubgroup g Z0) =
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) y) (bar M Q Z0) := by
    have hsub : conjSubgroup y (Z0.subgroupOf M) = (conjSubgroup g Z0).subgroupOf M := by
      ext z
      simp only [mem_conjSubgroup, Subgroup.mem_subgroupOf]
      rfl
    rw [show bar M Q Z0 = (Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) from rfl]
    rw [CFSG.GroupTheory.map_conjSubgroup, hsub]
    rfl
  have hconjEq : conjSubgroup x V =
      (bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z)) := by
    apply Subgroup.map_injective (f := (bar M Q (H0 M Z)).subtype)
      (bar M Q (H0 M Z)).subtype_injective
    calc (conjSubgroup x V).map (bar M Q (H0 M Z)).subtype
        = conjSubgroup (x : Mbar M Q) (V.map (bar M Q (H0 M Z)).subtype) :=
          (CFSG.GroupTheory.map_conjSubgroup (bar M Q (H0 M Z)).subtype V x).symm
      _ = conjSubgroup (x : Mbar M Q) (bar M Q Z0) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hbarZ0H]
      _ = bar M Q (conjSubgroup g Z0) := by
          rw [hy_eq]
          exact hconjBar.symm
      _ = ((bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z))).map
            (bar M Q (H0 M Z)).subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hbarconjH]
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hQCN : Q ≤ hc.CN t := sec8_Q_le_CN hc hs.toSec5.mem
  have hbarCNH : bar M Q (hc.CN t) ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hCNH0)
  have hleCN : conjSubgroup x V ≤ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    hxle.trans hO2
  have hsub : (bar M Q (conjSubgroup g Z0)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := hconjEq ▸ hleCN
  have hbarle : bar M Q (conjSubgroup g Z0) ≤ bar M Q (hc.CN t) := by
    have h := Subgroup.map_mono (f := (bar M Q (H0 M Z)).subtype) hsub
    rwa [Subgroup.map_subgroupOf_eq_of_le hbarconjH,
      Subgroup.map_subgroupOf_eq_of_le hbarCNH] at h
  refine ⟨g, hgM, ?_, ?_⟩
  · intro z hz
    have hzM : z ∈ M := conj_le_M hZ0M hgM hz
    have hmem : QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hzM⟩ ∈ bar M Q (conjSubgroup g Z0) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
    exact (mk_mem_bar_iff_sec4 hQCN ⟨z, hzM⟩).mp (hbarle hmem)
  · intro heq
    apply hxne
    rw [hconjEq, heq]

theorem pCore_two_MbarPrime_le_CN_of_fitting_sp
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :
    inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  let K : Subgroup (Mbar M Q) := bar M Q (NormH0 M Z Z0)
  let H : Subgroup (Mbar M Q) := bar M Q (H0 M Z)
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hKH : K ≤ H := MbarPrimeLe M Q Z Z0
  let e : ↥M' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hFK : generalizedFitting ↥K = (bar M Q (hc.CN t)).subgroupOf K := by
    simpa [K] using hF
  have hleF : pCore 2 ↥K ≤ generalizedFitting ↥K := by
    rw [generalizedFitting.eq_sup]
    exact (CFSG.pCore_le_fitting (G := ↥K) 2).trans le_sup_left
  have hpcK : pCore 2 ↥K ≤ (bar M Q (hc.CN t)).subgroupOf K := hleF.trans (le_of_eq hFK)
  have hmapP : (pCore 2 ↥M').map e.toMonoidHom = pCore 2 ↥K := CFSG.pCore_map_iso 2 e
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt hs.toSec5.mem
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hCNH0 : hc.CN t ≤ H0 M Z := fun y hy => hc.Rt_le_H0 t (Ctx.mem_CN.mp hy).1
  have hCNN : hc.CN t ≤ NormH0 M Z Z0 := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hCNH0 hy,
      IsCentrePre.mem_normalizer hZ0 hnormR (Ctx.mem_CN.mp hy).1⟩
  have hCNK : bar M Q (hc.CN t) ≤ K :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hCNN)
  have hKle : (pCore 2 ↥K).map K.subtype ≤ bar M Q (hc.CN t) :=
    calc (pCore 2 ↥K).map K.subtype
        ≤ ((bar M Q (hc.CN t)).subgroupOf K).map K.subtype := Subgroup.map_mono hpcK
      _ = bar M Q (hc.CN t) := Subgroup.map_subgroupOf_eq_of_le hCNK
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  have hea : e a ∈ pCore 2 ↥K := by
    rw [← hmapP]
    exact Subgroup.mem_map_of_mem e.toMonoidHom ha
  have hxbar : (M'.subtype a : Mbar M Q) ∈ bar M Q (hc.CN t) := by
    have h := hKle (Subgroup.mem_map_of_mem K.subtype hea)
    have hcoe : ((M'.subtype a : Hbar M Q Z) : Mbar M Q) = K.subtype (e a) := rfl
    rwa [hcoe]
  exact Subgroup.mem_subgroupOf.mpr hxbar

theorem bar_Z0_subgroupOf_le_pCore_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      inSubgroup (pCore 2) (MbarPrime M Q Z Z0) := by
  let V : Subgroup (Hbar M Q Z) := (bar M Q Z0).subgroupOf (bar M Q (H0 M Z))
  let M' : Subgroup (Hbar M Q Z) := MbarPrime M Q Z Z0
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
  have hE : Assembly.IsElemAbelian 2 V :=
    (isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0).subgroupOf (bar M Q (H0 M Z))
  have hVp : IsPGroup 2 ↥V := CFSG.Open.IsElemAbelian.isPGroup hE
  have hbarZ0K : bar M Q Z0 ≤ bar M Q (NormH0 M Z Z0) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M fun z hz =>
        Subgroup.mem_inf.mpr ⟨hZ0H hz, Z0.le_normalizer hz⟩)
  have hVle : V ≤ M' := fun v hv =>
    Subgroup.mem_subgroupOf.mpr (hbarZ0K (Subgroup.mem_subgroupOf.mp hv))
  have hM'norm : M' ≤ Subgroup.normalizer (V : Set (Hbar M Q Z)) := by
    have h := MbarPrime_eq_normalizer_bar_Z0_sp hc hs hZ0
    simpa [M', V] using h.le
  have hVnorm : (V.subgroupOf M').Normal := Subgroup.normal_subgroupOf_of_le_normalizer hM'norm
  have hVsubp : IsPGroup 2 (V.subgroupOf M') := hVp.comap_subtype
  have hle : V.subgroupOf M' ≤ pCore 2 ↥M' :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hVnorm hVsubp
  intro v hv
  exact Subgroup.mem_map.mpr ⟨⟨v, hVle hv⟩, hle (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

theorem exists_conj_le_CN_of_fitting_of_not_weaklyClosed_sp
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNWC : ¬ WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 :=
  exists_conj_le_CN_of_pCore_le_of_not_weaklyClosed_sp hc hs hZ0
    (bar_Z0_subgroupOf_le_pCore_sp h51 hA hc hs hZ0)
    (pCore_two_MbarPrime_le_CN_of_fitting_sp hc hs hZ0 hF) hNWC

theorem exists_isHMember_sp (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (h34 : Stroth34Statement) (hF2 : Step85F2Statement)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
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
    have hpc : pCore 2 (MbarPrime M Q Z Z0) =
        ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
          (MbarPrime M Q Z Z0) := by
      rw [← generalizedFitting_MbarPrime_sp hc hs hZ0 hF2]
      exact generalizedFitting_MbarPrime_eq_of_fitting hF
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
