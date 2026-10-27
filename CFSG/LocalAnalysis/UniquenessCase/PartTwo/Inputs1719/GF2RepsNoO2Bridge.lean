module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436
public import CFSG.Quasithin.Vol2.Ch3xModule
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.ElemAbelianMap
public import CFSG.Quasithin.Background.F918J3
public import CFSG.CGT.PushingUpLit.BHS.TwoSixteenAlt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InF InFFor)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem o2Trivial_iff_pCoreOf_eq_bot {Y : Subgroup (MulAut W)} :
    O2Trivial Y ↔ pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQle : pCoreOf 2 Y ≤ Y :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  constructor
  · intro h
    exact h _ hQle ((Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  · intro h P hPY hPn hP2
    have hPY' : Y ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mp hPn
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPY hPY' hP2
    rw [h] at hle
    exact le_bot_iff.mp hle

theorem inf_centSub_fixV_pCoreOf_eq {Y L T : Subgroup (MulAut W)}
    (hw : ∀ w : W, w ^ 2 = 1) (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) :
    Y ⊓ centSub (fixV (pCoreOf 2 Y)) =
      pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (MulAut W) := pCoreOf 2 Y with hQ
  have hQle : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hLQ : ∀ l ∈ L, ∀ q ∈ Q, l * q = q * l := by
    intro l hl q hq
    have hmem : ⁅l, q⁆ ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← CFSG.Quasithin.H13.Ch4.commutator_eq_bot_of_isComponentOf hcomp
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)]
      exact Subgroup.commutator_mem_commutator hl hq
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  set X : Subgroup (MulAut W) := CFSG.Quasithin.conjClosure L T with hX
  have hLX : L ≤ X := CFSG.Quasithin.le_conjClosure L T
  have hXY : X ≤ Y := by
    refine CFSG.Quasithin.conjClosure_le fun t ht z hz => ?_
    exact Y.mul_mem (Y.mul_mem (hTY ht) (hLY hz)) (Y.inv_mem (hTY ht))
  have hYX : Y = X ⊔ T := by
    refine le_antisymm ?_ (sup_le hXY hTY)
    rw [← hLT]
    exact sup_le_sup hLX le_rfl
  have hXQ : X ≤ Subgroup.centralizer (Q : Set (MulAut W)) := by
    refine CFSG.Quasithin.conjClosure_le fun t ht z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : t⁻¹ * q * t ∈ Q :=
      B1Red.conj_mem_pCoreOf (Y.inv_mem (hTY ht)) hq
    have hzq : z * (t⁻¹ * q * t) = (t⁻¹ * q * t) * z := hLQ z hz _ hq'
    have hzc : z * (t⁻¹ * q * t) * z⁻¹ = t⁻¹ * q * t := by
      rw [hzq, mul_assoc, mul_inv_cancel, mul_one]
    have hxq : (t * z * t⁻¹) * q * (t * z * t⁻¹)⁻¹ = q := by
      calc (t * z * t⁻¹) * q * (t * z * t⁻¹)⁻¹
          = t * (z * (t⁻¹ * q * t) * z⁻¹) * t⁻¹ := by group
        _ = t * (t⁻¹ * q * t) * t⁻¹ := by rw [hzc]
        _ = q := by group
    have hxq2 : (t * z * t⁻¹) * q = q * (t * z * t⁻¹) := by
      have h := congrArg (fun y => y * (t * z * t⁻¹)) hxq
      calc (t * z * t⁻¹) * q
          = (t * z * t⁻¹) * q * (t * z * t⁻¹)⁻¹ * (t * z * t⁻¹) := by group
        _ = q * (t * z * t⁻¹) := h
    exact hxq2.symm
  have hD : ∀ x ∈ Y, Odd (orderOf x) → x ∈ X := by
    intro x hx ho
    have hx' : x ∈ X ⊔ T := by rwa [← hYX]
    have hDN : X ⊔ T ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
      sup_le Subgroup.le_normalizer (CFSG.Quasithin.le_normalizer_conjClosure L T)
    obtain ⟨k, hk⟩ := CFSG.Quasithin.B6.isTwoQuotient_of_sup_eq (C := X) (D := X ⊔ T)
      (T := T) hsyl.isPGroup hDN (sup_comm T X) x hx'
    exact CFSG.Quasithin.Ch3x.mem_of_pow_two_pow_mem_of_odd (N := X) ho hk
  have hDQ : ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x := by
    intro x hx q hq
    exact (Subgroup.mem_centralizer_iff.mp (hXQ hx) q hq).symm
  exact B1Red.kernel_eq_pCoreOf hw hD hDQ

theorem o2Trivial_autSub {Y L T : Subgroup (MulAut W)}
    (hw : ∀ w : W, w ^ 2 = 1) (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y)
    (hcomp : IsComponentOf L Y) (hsyl : IsSylowIn 2 T Y) :
    O2Trivial (autSub Y (fixV (pCoreOf 2 Y))) := by
  rw [o2Trivial_iff_pCoreOf_eq_bot]
  exact B1Red.pCoreOf_autSub_eq_bot (inf_centSub_fixV_pCoreOf_eq hw hLY hTY hLT hcomp hsyl)

theorem inf_pCoreOf_eq_bot_of_odd_center {Y L : Subgroup (MulAut W)}
    (hcomp : IsComponentOf L Y) (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    L ⊓ pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hcomp.2.2
  have hQle : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  set Q : Subgroup (MulAut W) := pCoreOf 2 Y with hQ
  set N : Subgroup (MulAut W) := L ⊓ Q with hN
  have hNn : (N.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr fun x l hx hl => ?_
    exact ⟨L.mul_mem (L.mul_mem hl hx.1) (L.inv_mem hl),
      B1Red.conj_mem_pCoreOf (hcomp.1 hl) hx.2⟩
  have hNne : (N.subgroupOf L) ≠ ⊤ := by
    intro htop
    have hLQ : L ≤ Q := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hx').2
    haveI : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥L
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hLQ).isNilpotent
  have hcen := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hcomp.2.2 _
    hNne
  have hdvd : Nat.card ↥(N.subgroupOf L) ∣ Nat.card (Subgroup.center ↥L) :=
    Subgroup.card_dvd_of_le hcen
  have hcard : Nat.card ↥(N.subgroupOf L) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard] at hdvd
  have hoddN : Odd (Nat.card ↥N) := Odd.of_dvd_nat hodd hdvd
  have h2N : IsPGroup 2 ↥N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_right
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2N
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have h2dvd : 2 ∣ Nat.card ↥N := by
        rw [hk]
        exact dvd_pow_self 2 h.ne'
      exact (Nat.not_even_iff_odd.mpr hoddN) (even_iff_two_dvd.mpr h2dvd)
  have hcard1 : Nat.card ↥N = 1 := by rw [hk, hk0, pow_zero]
  have hbot : N = ⊥ := Subgroup.card_eq_one.mp hcard1
  exact hbot

theorem inf_pCoreOf_le_centralizer_of_isComponent {Y L : Subgroup (MulAut W)}
    (hcomp : IsComponentOf L Y) :
    L ⊓ pCoreOf 2 Y ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (MulAut W) := pCoreOf 2 Y with hQ
  set N : Subgroup (MulAut W) := L ⊓ Q with hN
  have hNn : (N.subgroupOf L).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr fun x l hx hl => ?_
    exact ⟨L.mul_mem (L.mul_mem hl hx.1) (L.inv_mem hl),
      B1Red.conj_mem_pCoreOf (hcomp.1 hl) hx.2⟩
  have hNne : (N.subgroupOf L) ≠ ⊤ := by
    intro htop
    have hLQ : L ≤ Q := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hx').2
    have hq : CFSG.IsQuasisimple ↥L :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hcomp.2.2
    haveI : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hperf : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.not_isNilpotent ↥L
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le hLQ).isNilpotent
  have hcen := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hcomp.2.2 _
    hNne
  intro x hx
  have hxL : x ∈ L := hx.1
  have hxN : (⟨x, hxL⟩ : ↥L) ∈ N.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
  have hxZ := hcen hxN
  rw [Subgroup.mem_center_iff] at hxZ
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (hxZ ⟨y, hy⟩)

theorem isComponentOf_autSub {Y L : Subgroup (MulAut W)} {U : Subgroup W}
    (hLY : L ≤ Y) (hstab : Y ≤ stabSub U) (hcomp : IsComponentOf L Y)
    (hLnc : ¬ L ≤ centSub U) : IsComponentOf (autSub L U) (autSub Y U) := by
  have hLstab : L ≤ stabSub U := hLY.trans hstab
  refine ⟨autSub_mono hLY U, ?_, B1Red.isQuasisimple_autSub hLstab hcomp.2.2 hLnc⟩
  have hcomp_top : CFSG.Open.IsComponentOf (L.subgroupOf Y) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.top_iff.mpr hcomp.2.1.subgroupOf,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hcomp.2.2⟩
  have hmap1 : (L.subgroupOf Y).map (resHomOn U hstab) = autSub L U := by
    rw [autSub_eq_range_resHomOn hLstab]
    ext f
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : MulAut W), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨⟨(l : MulAut W), hLY l.2⟩, l.2, rfl⟩
  have hmap2 : (⊤ : Subgroup ↥Y).map (resHomOn U hstab) = autSub Y U := by
    rw [← MonoidHom.range_eq_map, autSub_eq_range_resHomOn hstab]
  rw [← hmap1, ← hmap2]
  exact CFSG.Open.IsSubnormal.map (f := resHomOn U hstab) hcomp_top.2.1

theorem map_fixV_autSub {Y X : Subgroup (MulAut W)} {U : Subgroup W}
    (hXY : X ≤ Y) (hstab : Y ≤ stabSub U) (hXU : fixV X ≤ U) :
    (fixV (autSub X U)).map U.subtype = fixV X := by
  rw [map_subtype_fixV_autSub (hXY.trans hstab)]
  exact inf_eq_right.mpr hXU

theorem fixV_autSub_ne {Y T : Subgroup (MulAut W)}
    (hTY : T ≤ Y) (hQleT : pCoreOf 2 Y ≤ T) (hfix : fixV T ≠ fixV Y) :
    fixV (autSub T (fixV (pCoreOf 2 Y))) ≠ fixV (autSub Y (fixV (pCoreOf 2 Y))) := by
  have hst : Y ≤ stabSub (fixV (pCoreOf 2 Y)) := B1Red.le_stabSub_fixV_pCoreOf Y
  intro h
  apply hfix
  have hmap := congrArg (Subgroup.map (fixV (pCoreOf 2 Y)).subtype) h
  rw [map_fixV_autSub hTY hst (fixV_anti hQleT),
    map_fixV_autSub (le_rfl : Y ≤ Y) hst
      (fixV_anti (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))] at hmap
  exact hmap

theorem isSylowIn_autSub {Y T : Subgroup (MulAut W)}
    (hTY : T ≤ Y) (hQleT : pCoreOf 2 Y ≤ T)
    (hker : Y ⊓ centSub (fixV (pCoreOf 2 Y)) = pCoreOf 2 Y)
    (hsyl : IsSylowIn 2 T Y) :
    IsSylowIn 2 (autSub T (fixV (pCoreOf 2 Y))) (autSub Y (fixV (pCoreOf 2 Y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst : Y ≤ stabSub (fixV (pCoreOf 2 Y)) := B1Red.le_stabSub_fixV_pCoreOf Y
  have hstT : T ≤ stabSub (fixV (pCoreOf 2 Y)) := hTY.trans hst
  have hT2 : IsPGroup 2 ↥(autSub T (fixV (pCoreOf 2 Y))) :=
    ((hsyl.isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hstT).symm).map
      (resHom (fixV (pCoreOf 2 Y)))
  have hYbar : Nat.card (autSub Y (fixV (pCoreOf 2 Y))) * Nat.card ↥(pCoreOf 2 Y) =
      Nat.card Y := by
    have h := card_autSub_mul hst
    rwa [hker] at h
  have hTbar : Nat.card (autSub T (fixV (pCoreOf 2 Y))) * Nat.card ↥(pCoreOf 2 Y) =
      Nat.card T := by
    have h := card_autSub_mul hstT
    have h2 : T ⊓ centSub (fixV (pCoreOf 2 Y)) = pCoreOf 2 Y := by
      refine le_antisymm ?_ ?_
      · intro x hx
        exact hker ▸ (show x ∈ Y ⊓ centSub (fixV (pCoreOf 2 Y)) from ⟨hTY hx.1, hx.2⟩)
      · intro x hx
        have hx' : x ∈ Y ⊓ centSub (fixV (pCoreOf 2 Y)) := by rw [hker]; exact hx
        exact ⟨hQleT hx, hx'.2⟩
    rwa [h2] at h
  have hrel : (autSub T (fixV (pCoreOf 2 Y))).relIndex (autSub Y (fixV (pCoreOf 2 Y))) *
        Nat.card (autSub T (fixV (pCoreOf 2 Y))) =
      Nat.card (autSub Y (fixV (pCoreOf 2 Y))) := by
    simpa [inf_eq_left.mpr (autSub_mono hTY (fixV (pCoreOf 2 Y)))] using
      Subgroup.relIndex_mul_card (autSub T (fixV (pCoreOf 2 Y)))
        (autSub Y (fixV (pCoreOf 2 Y)))
  have hrelT : T.relIndex Y * Nat.card T = Nat.card Y := by
    simpa [inf_eq_left.mpr hTY] using Subgroup.relIndex_mul_card T Y
  have hposT : 0 < Nat.card (autSub T (fixV (pCoreOf 2 Y))) := Nat.card_pos
  have hposQ : 0 < Nat.card ↥(pCoreOf 2 Y) := Nat.card_pos
  have h1 : (autSub T (fixV (pCoreOf 2 Y))).relIndex (autSub Y (fixV (pCoreOf 2 Y))) *
        Nat.card (autSub T (fixV (pCoreOf 2 Y))) * Nat.card ↥(pCoreOf 2 Y) =
      T.relIndex Y * Nat.card (autSub T (fixV (pCoreOf 2 Y))) *
        Nat.card ↥(pCoreOf 2 Y) := by
    calc (autSub T (fixV (pCoreOf 2 Y))).relIndex (autSub Y (fixV (pCoreOf 2 Y))) *
          Nat.card (autSub T (fixV (pCoreOf 2 Y))) * Nat.card ↥(pCoreOf 2 Y)
        = Nat.card (autSub Y (fixV (pCoreOf 2 Y))) * Nat.card ↥(pCoreOf 2 Y) := by rw [hrel]
      _ = Nat.card Y := hYbar
      _ = T.relIndex Y * Nat.card T := hrelT.symm
      _ = T.relIndex Y * (Nat.card (autSub T (fixV (pCoreOf 2 Y))) *
            Nat.card ↥(pCoreOf 2 Y)) := by rw [hTbar]
      _ = T.relIndex Y * Nat.card (autSub T (fixV (pCoreOf 2 Y))) *
            Nat.card ↥(pCoreOf 2 Y) := by ring
  have heq : (autSub T (fixV (pCoreOf 2 Y))).relIndex
      (autSub Y (fixV (pCoreOf 2 Y))) = T.relIndex Y := by
    refine Nat.eq_of_mul_eq_mul_right hposT ?_
    exact Nat.eq_of_mul_eq_mul_right hposQ h1
  refine ⟨autSub_mono hTY (fixV (pCoreOf 2 Y)), hT2, ?_⟩
  rw [heq]
  exact hsyl.not_dvd_relIndex

theorem aSet_autSub {W : Type} [CommGroup W] [Finite W] {Y A : Subgroup (MulAut W)}
    {U : Subgroup W} {k : ℕ} (hAY : A ≤ Y) (hstab : Y ≤ stabSub U)
    (hA : A ∈ E3.aSet k Y) (hAnc : ¬ A ≤ centSub U) :
    autSub A U ∈ E3.aSet k (autSub Y U) := by
  obtain ⟨-, -, hAel, hAfix⟩ := hA
  have hAstab : A ≤ stabSub U := hAY.trans hstab
  refine ⟨autSub_mono hAY U, ?_, ?_, ?_⟩
  · intro h
    exact hAnc fun g hg u hu => ((B1.autSub_eq_bot_iff hAstab).mp h) hu g hg
  · have hc : ∀ a ∈ A.subgroupOf (stabSub U), ∀ b ∈ A.subgroupOf (stabSub U), a * b = b * a := by
      intro a ha b hb
      exact Subtype.ext (hAel.1 a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
        (Subgroup.mem_subgroupOf.mp hb))
    have hs : ∀ a ∈ A.subgroupOf (stabSub U), a * a = 1 := by
      intro a ha
      exact Subtype.ext (by
        simpa [pow_two] using hAel.2 a.1 (Subgroup.mem_subgroupOf.mp ha))
    exact CFSG.ASVolI.ChH.isElemAbelian2_map_of_comm_sq (resHom U)
      (A.subgroupOf (stabSub U)) hc hs
  · intro D hD hmD
    have hBle : B1.preB A U D ≤ A := B1.preB_le A U D
    have hBstab : B1.preB A U D ≤ stabSub U := B1.preB_le_stabSub hAstab D
    have hDB : autSub (B1.preB A U D) U = D := B1.autSub_preB hD
    have hBcent : B1.preB A U D ⊓ centSub U = A ⊓ centSub U :=
      le_antisymm (inf_le_inf_right _ hBle)
        (le_inf (B1.inf_centSub_le_preB hAstab D) inf_le_right)
    have hcardA : Nat.card (autSub A U) * Nat.card ↥(A ⊓ centSub U) = Nat.card A :=
      card_autSub_mul hAstab
    have hcardB : Nat.card D * Nat.card ↥(A ⊓ centSub U) = Nat.card ↥(B1.preB A U D) := by
      have h := card_autSub_mul hBstab
      rw [hDB, hBcent] at h
      exact h
    have hrA : (B1.preB A U D).relIndex A * Nat.card ↥(B1.preB A U D) = Nat.card A := by
      have h := Subgroup.relIndex_mul_card (H := B1.preB A U D) (K := A)
      rwa [inf_eq_left.mpr hBle] at h
    have hrD : D.relIndex (autSub A U) * Nat.card D = Nat.card (autSub A U) := by
      have h := Subgroup.relIndex_mul_card (H := D) (K := autSub A U)
      rwa [inf_eq_left.mpr hD] at h
    have hrel : (B1.preB A U D).relIndex A = D.relIndex (autSub A U) := by
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(B1.preB A U D))) ?_
      rw [hrA, ← hcardA, ← hrD, ← hcardB]
      ring
    have hmB : E3.mQuot A (B1.preB A U D) < k := by
      have h : E3.mQuot A (B1.preB A U D) = E3.mQuot (autSub A U) D := by
        simp only [E3.mQuot, hrel]
      rwa [h]
    have hfix : fixV (B1.preB A U D) = fixV A := hAfix (B1.preB A U D) hBle hmB
    have hmaps : (fixV D).map U.subtype = (fixV (autSub A U)).map U.subtype := by
      rw [← hDB, map_subtype_fixV_autSub hBstab, map_subtype_fixV_autSub hAstab, hfix]
    exact Subgroup.map_injective U.subtype_injective hmaps

theorem bParam_le_autSub {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {U : Subgroup W} (hLY : L ≤ Y) (hstab : Y ≤ stabSub U)
    (hne : ∀ (k : ℕ) (A : Subgroup (MulAut W)),
      A ∈ E3.aSet k Y →
      ⁅L, A⁆ ≠ ⊥ → ⁅autSub L U, autSub A U⁆ ≠ ⊥) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam L Y ≤
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam (autSub L U) (autSub Y U) := by
  unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam
  by_cases hne' : {k : ℕ | 0 < k ∧ ∃ A ∈ E3.aSet k Y, ⁅L, A⁆ ≠ ⊥}.Nonempty
  · refine csSup_le hne' ?_
    rintro k ⟨hk, A, hA, hneA⟩
    have hAY : A ≤ Y := hA.1
    have hAnc : ¬ A ≤ centSub U := by
      intro hc
      have hbot : autSub A U = ⊥ :=
        (B1.autSub_eq_bot_iff (hAY.trans hstab)).mpr fun u hu g hg => hc hg u hu
      exact hne k A hA hneA (by rw [hbot, Subgroup.commutator_bot_right])
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_bParam hk
      (aSet_autSub hAY hstab hA hAnc) (hne k A hA hneA)
  · rw [Set.not_nonempty_iff_eq_empty] at hne'
    rw [hne']
    have h0 : sSup (∅ : Set ℕ) = 0 := by simp
    rw [h0]
    exact Nat.zero_le _

theorem commutator_autSub_ne_bot_of_centralizer {Y L A : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hAY : A ≤ Y) (hstab : Y ≤ stabSub (fixV (pCoreOf 2 Y)))
    (hker : Y ⊓ centSub (fixV (pCoreOf 2 Y)) = pCoreOf 2 Y)
    (hLQcomm : ⁅L, pCoreOf 2 Y⁆ = ⊥)
    (hLcent : L ⊓ pCoreOf 2 Y ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hLperf : ⁅L, L⁆ = L) (hne : ⁅L, A⁆ ≠ ⊥) :
    ⁅autSub L (fixV (pCoreOf 2 Y)), autSub A (fixV (pCoreOf 2 Y))⁆ ≠ ⊥ := by
  intro hbot
  set U : Subgroup W := fixV (pCoreOf 2 Y) with hU
  have hcommLQ : ∀ l ∈ L, ∀ q ∈ pCoreOf 2 Y, l * q = q * l := by
    intro l hl q hq
    have hmem : ⁅l, q⁆ ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hLQcomm]
      exact Subgroup.commutator_mem_commutator hl hq
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hK : ⁅L, A⁆ ≤ pCoreOf 2 Y := by
    rw [Subgroup.commutator_le]
    intro l hl a ha
    have hxY : ⁅l, a⁆ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem (hLY hl) (hAY ha)) (Y.inv_mem (hLY hl)))
        (Y.inv_mem (hAY ha))
    have hres : (⟨⁅l, a⁆, hxY⟩ : ↥Y) ∈ (resHomOn U hstab).ker := by
      rw [MonoidHom.mem_ker]
      have h1 : resHomOn U hstab ⟨⁅l, a⁆, hxY⟩ =
          ⁅resHomOn U hstab ⟨l, hLY hl⟩, resHomOn U hstab ⟨a, hAY ha⟩⁆ := by
        have hdecomp : (⟨⁅l, a⁆, hxY⟩ : ↥Y) =
            ⁅(⟨l, hLY hl⟩ : ↥Y), (⟨a, hAY ha⟩ : ↥Y)⁆ := Subtype.ext rfl
        rw [hdecomp, map_commutatorElement]
      rw [h1]
      have hmem : ⁅resHomOn U hstab ⟨l, hLY hl⟩, resHomOn U hstab ⟨a, hAY ha⟩⁆ ∈
          ⁅autSub L U, autSub A U⁆ := by
        refine Subgroup.commutator_mem_commutator ?_ ?_
        · rw [autSub_eq_map_resHomOn hLY hstab]
          exact Subgroup.mem_map_of_mem _ hl
        · rw [autSub_eq_map_resHomOn hAY hstab]
          exact Subgroup.mem_map_of_mem _ ha
      rw [hbot] at hmem
      simpa using hmem
    have hker' : (resHomOn U hstab).ker = (Y ⊓ centSub U).subgroupOf Y := by
      ext x
      simp only [resHomOn, MonoidHom.mem_ker, MonoidHom.comp_apply, ker_resHom,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨x.2, ?_⟩
        have h' : (Subgroup.inclusion hstab x) ∈ (resHom U).ker := by simpa using h
        rwa [ker_resHom, Subgroup.mem_subgroupOf] at h'
      · rintro ⟨-, h⟩
        show (Subgroup.inclusion hstab x) ∈ (resHom U).ker
        rw [ker_resHom, Subgroup.mem_subgroupOf]
        exact h
    rw [hker', Subgroup.mem_subgroupOf, hker] at hres
    simpa using hres
  have hQN : pCoreOf 2 Y ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : L.map (MulAut.conj q).toMonoidHom ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      change (MulAut.conj q) x ∈ L
      have heq : (MulAut.conj q) x = x := by
        rw [MulAut.conj_apply, ← hcommLQ x hx q hq, mul_assoc, mul_inv_cancel, mul_one]
      rwa [heq]
    exact Subgroup.eq_of_le_of_card_ge h1
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj q).injective).symm)
  have hAN : A ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 Y : Subgroup (MulAut W)) : Set _) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 : (L ⊔ pCoreOf 2 Y).map (MulAut.conj a).toMonoidHom ≤ L ⊔ pCoreOf 2 Y := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        have hc : ⁅a, x⁆ ∈ pCoreOf 2 Y := by
          have hmem : ⁅a, x⁆ ∈ ⁅A, L⁆ := Subgroup.commutator_mem_commutator ha hx
          rw [Subgroup.commutator_comm A L] at hmem
          exact hK hmem
        have he : (MulAut.conj a) x = ⁅a, x⁆ * x := by
          rw [MulAut.conj_apply, commutatorElement]
          group
        change (MulAut.conj a) x ∈ L ⊔ pCoreOf 2 Y
        rw [he]
        exact (L ⊔ pCoreOf 2 Y).mul_mem (Subgroup.mem_sup_right hc)
          (Subgroup.mem_sup_left hx)
      · rintro _ ⟨q, hq, rfl⟩
        exact Subgroup.mem_sup_right (B1Red.conj_mem_pCoreOf (hAY ha) hq)
    exact Subgroup.eq_of_le_of_card_ge h1
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm)
  have hpc : perfectCore (L ⊔ pCoreOf 2 Y) = L := by
    refine le_antisymm ?_ (le_perfectCore_of_perfect le_sup_left hLperf)
    refine perfectCore_le_of_sup_solvable (A := L) (B := pCoreOf 2 Y)
      (Y := L ⊔ pCoreOf 2 Y) le_sup_left ?_ rfl ?_
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hQN)
    · have : Group.IsNilpotent ↥(pCoreOf 2 Y) :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).isNilpotent
      infer_instance
  have hAN' : ∀ a ∈ A, L.map (MulAut.conj a).toMonoidHom = L := by
    intro a ha
    have hmap : (L ⊔ pCoreOf 2 Y).map (MulAut.conj a).toMonoidHom = L ⊔ pCoreOf 2 Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAN ha)
    calc L.map (MulAut.conj a).toMonoidHom
        = (perfectCore (L ⊔ pCoreOf 2 Y)).map (MulAut.conj a).toMonoidHom := by rw [hpc]
      _ = perfectCore ((L ⊔ pCoreOf 2 Y).map (MulAut.conj a).toMonoidHom) :=
          map_perfectCore _ _
      _ = perfectCore (L ⊔ pCoreOf 2 Y) := by rw [hmap]
      _ = L := hpc
  have hKL : ⁅L, A⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro l hl a ha
    have hla : (MulAut.conj a) l⁻¹ ∈ L := by
      rw [← hAN' a ha]
      exact Subgroup.mem_map_of_mem _ (L.inv_mem hl)
    have he : ⁅l, a⁆ = l * (MulAut.conj a) l⁻¹ := by
      rw [MulAut.conj_apply, commutatorElement]
      group
    rw [he]
    exact L.mul_mem hl hla
  have hZ : ⁅L, A⁆ ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    (le_inf hKL hK).trans hLcent
  have h1 : ⁅⁅L, A⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZ
  have h2 : ⁅⁅A, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm A L]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := A)
    h1 h2
  rw [hLperf] at h3
  exact hne h3

structure NoO2NormalSetup {Y L T : Subgroup (MulAut W)} (hLY : L ≤ Y) where
  U : Subgroup W
  Q : Subgroup (MulAut W)
  Lb : Subgroup (MulAut U)
  Yb : Subgroup (MulAut U)
  Tb : Subgroup (MulAut U)
  e : ↥L ≃* ↥Lb
  φ : ↥L →* MulAut U
  hst : Y ≤ stabSub U
  hker : Y ⊓ centSub U = Q
  hQleT : Q ≤ T
  he_apply : ∀ x : ↥L, φ x = resHomOn U (hLY.trans hst) x
  hwU : ∀ u : U, u ^ 2 = 1
  hLbYb : Lb ≤ Yb
  hTbYb : Tb ≤ Yb
  hsupb : Lb ⊔ Tb = Yb
  hcompb : IsComponentOf Lb Yb
  hsylb : IsSylowIn 2 Tb Yb
  hfixb : fixV Tb ≠ fixV Yb
  hO2b : O2Trivial Yb
  hb : bParam L Y ≤ bParam Lb Yb

@[expose] noncomputable def noO2NormalSetup (hw : ∀ w : W, w ^ 2 = 1)
    {Y L T : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hTY : T ≤ Y) (hLT : L ⊔ T = Y) (hcomp : IsComponentOf L Y)
    (hsyl : IsSylowIn 2 T Y) (hfix : fixV T ≠ fixV Y)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) :
    NoO2NormalSetup (Y := Y) (L := L) (T := T) hLY := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup (MulAut W) := pCoreOf 2 Y with hQ
  set U : Subgroup W := fixV Q with hU
  have hst : Y ≤ stabSub U := B1Red.le_stabSub_fixV_pCoreOf Y
  set Lb : Subgroup (MulAut U) := autSub L U with hLb
  set Yb : Subgroup (MulAut U) := autSub Y U with hYb
  set Tb : Subgroup (MulAut U) := autSub T U with hTb
  have hker : Y ⊓ centSub U = Q :=
    inf_centSub_fixV_pCoreOf_eq hw hLY hTY hLT hcomp hsyl
  have hLQ : L ⊓ Q = ⊥ := inf_pCoreOf_eq_bot_of_odd_center hcomp hodd
  have hLQcomm : ⁅L, Q⁆ = ⊥ :=
    CFSG.Quasithin.H13.Ch4.commutator_eq_bot_of_isComponentOf hcomp
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hLcent : L ⊓ Q ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    inf_pCoreOf_le_centralizer_of_isComponent hcomp
  have hQleT : Q ≤ T :=
    hsyl.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hcomp.2.2
  have hLperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hq.1.commutator_eq_top, Subgroup.map_top,
      Subgroup.range_subtype]
  have hfaith : L ⊓ centSub U = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxQ : x ∈ Q := by
      rw [← hker]
      exact ⟨hLY hx.1, hx.2⟩
    have hxLQ : x ∈ L ⊓ Q := ⟨hx.1, hxQ⟩
    simpa [hLQ] using hxLQ
  have hqL : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have hLnc : ¬ L ≤ centSub U := by
    intro hle
    have hLbot : L ≤ (⊥ : Subgroup (MulAut W)) := by
      have h1 : L ≤ L ⊓ centSub U := le_inf le_rfl hle
      rwa [hfaith] at h1
    haveI : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance (le_bot_iff.mp hLbot)
  have hqb : CFSG.Open.IsQuasisimple ↥Lb :=
    B1Red.isQuasisimple_autSub (hLY.trans hst) hqL hLnc
  set e : ↥L ≃* ↥Lb := autSubEquivOfFaithful (hLY.trans hst) hfaith with he
  let φ : ↥L →* MulAut U := Lb.subtype.comp e.toMonoidHom
  have he_apply : ∀ x : ↥L, φ x = resHomOn U (hLY.trans hst) x := by
    intro x
    show ((e x : ↥Lb) : MulAut U) = resHomOn U (hLY.trans hst) x
    rw [he]
    exact autSubEquivOfFaithful_apply (hLY.trans hst) hfaith x
  have hcompb : IsComponentOf Lb Yb :=
    isComponentOf_autSub hLY hst hcomp hLnc
  have hsylb : IsSylowIn 2 Tb Yb := isSylowIn_autSub hTY hQleT hker hsyl
  have hfixb : fixV Tb ≠ fixV Yb := fixV_autSub_ne hTY hQleT hfix
  have hO2b : O2Trivial Yb := o2Trivial_autSub hw hLY hTY hLT hcomp hsyl
  have hLbYb : Lb ≤ Yb := autSub_mono hLY U
  have hTbYb : Tb ≤ Yb := autSub_mono hTY U
  have hsupb : Lb ⊔ Tb = Yb := by
    have h1 := CFSG.CGT.PushingUpLit.BHS.autSub_sup (hLY.trans hst) (hTY.trans hst)
    rw [hLT] at h1
    simpa only [Lb, Tb, Yb] using h1.symm
  have hne : ∀ (k : ℕ) (A : Subgroup (MulAut W)), A ∈ E3.aSet k Y → ⁅L, A⁆ ≠ ⊥ →
      ⁅autSub L U, autSub A U⁆ ≠ ⊥ := by
    intro k A hA hneA
    exact commutator_autSub_ne_bot_of_centralizer hLY hA.1 hst hker hLQcomm hLcent
      hLperf hneA
  have hb : bParam L Y ≤ bParam Lb Yb := bParam_le_autSub hLY hst hne
  have hwU : ∀ u : ↥U, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    simpa using hw (u : W)
  exact ⟨U, Q, Lb, Yb, Tb, e, φ, hst, hker, hQleT, he_apply, hwU, hLbYb, hTbYb,
    hsupb, hcompb, hsylb, hfixb, hO2b, hb⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
