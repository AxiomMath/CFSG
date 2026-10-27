module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Single

import CFSG.RankThree.GF2n.Stroth78.Sec3OddInvariant
import CFSG.LinearAlgebra.F2PlaneMaps
import CFSG.GroupTheory.OddOrderClosurePerfect
import CFSG.LocalAnalysis.RankThreeUC.Section5.OpenPCoreEq
import CFSG.LargeExtraspecial.OrthoF2PairsCases
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.RankThree.GF2n.Stroth78.Sec2Five
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.GroupTheory.Fitting.SmallGeneralizedFitting

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoLin_apply_eq_self_of_perfect (S : Setting z E F) {Y : Subgroup (Hbar z)}
    (hY : ⁅Y, Y⁆ = Y) {x : Hbar z} (hx : x ∈ A2set S)
    (hYx : ∀ y ∈ Y, y * x = x * y) :
    ∀ y ∈ Y, ∀ v ∈ commSpace (rhoLin S x), rhoLin S y v = v := by
  letI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  have hW : finrank (ZMod 2) (commSpace (rhoLin S x)) = 2 :=
    finrank_commSpace_rhoLin_eq_two S hx
  have hst : ∀ g : ↥Y, ∀ w ∈ commSpace (rhoLin S x),
      rhoGL S (g : Hbar z) w ∈ commSpace (rhoLin S x) := by
    intro g w hw
    have hcomm : rhoLin S (g : Hbar z) * rhoLin S x = rhoLin S x * rhoLin S (g : Hbar z) := by
      have h := congrArg (rhoLin S) (hYx (g : Hbar z) g.2)
      simpa [rhoLin_mul] using h
    exact CFSG.LargeExtraspecial.AS35QCo.apply_mem_commSpace hcomm hw
  have hall := CFSG.LinearAlgebra.apply_eq_self_of_isPerfect
    (W := commSpace (rhoLin S x)) hW ((rhoGL S).comp Y.subtype) hst
  intro y hy v hv
  exact hall ⟨y, hy⟩ v hv

theorem aVec_not_mem_iSup_commSpace_of_trivial (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {ω : Hbar z} (hω3 : orderOf ω = 3)
    (haω : aVec S h.mem_Q ∈ commSpace (rhoLin S ω)) {Y : Subgroup (Hbar z)}
    (hY : ∀ y ∈ Y, ∀ v ∈ commSpace (rhoLin S ω), rhoLin S y v = v) :
    aVec S h.mem_Q ∉ ⨆ y ∈ Y, commSpace (rhoLin S y) := by
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hωq : ∀ v, qS S (rhoLin S ω v) = qS S v :=
    fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S ω).2 v
  have hbot : commSpace (rhoLin S ω) ⊓ fixSpace (rhoLin S ω) = ⊥ :=
    CFSG.LargeExtraspecial.OrthoF2.commSpace_inf_fixSpace_eq_bot_of_pow_three
      (rhoLin_pow_three_eq_one S hω3)
  have hna : aVec S h.mem_Q ∉ fixSpace (rhoLin S ω) := by
    intro hmem
    have hmem' : aVec S h.mem_Q ∈ commSpace (rhoLin S ω) ⊓ fixSpace (rhoLin S ω) :=
      Submodule.mem_inf.mpr ⟨haω, hmem⟩
    rw [hbot, Submodule.mem_bot] at hmem'
    exact aV_ne_zero S h.mem_Q h.not_mem_ZQ hmem'
  have hle : (⨆ y ∈ Y, commSpace (rhoLin S y)) ≤ fixSpace (rhoLin S ω) := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    have hyq : ∀ v, qS S (rhoLin S y v) = qS S v :=
      fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S y).2 v
    exact CFSG.LargeExtraspecial.AS35QCo.commSpace_le_fixSpace_swap
      (hq := by letI := modAbF S; exact q_nondegenerate S) hωq hyq
      (fun v hv => mem_fixSpace.mpr (hY y hy v hv))
  exact fun hmem => hna (hle hmem)

theorem eq_bot_of_le_normalizer_of_isPGroup_two (S : Setting z E F) {Y : Subgroup (Hbar z)}
    (hYn : Y.Normal) {P : Subgroup (Hbar z)} (hPY : P ≤ Y) (hP2 : IsPGroup 2 P)
    (hnorm : Y ≤ Subgroup.normalizer (P : Set (Hbar z))) : P = ⊥ := by
  have hPcore : P ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hPY hnorm hP2
  haveI : Y.Normal := hYn
  have hcoreNormal : (pCoreOf 2 Y).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := Y) (K := CFSG.pCore 2 Y)
  have hcoreLe : pCoreOf 2 Y ≤ CFSG.pCore 2 (Hbar z) :=
    CFSG.LieType.BorelTits.le_pCore 2 hcoreNormal
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  rw [pCore_two_Hbar_eq_bot S] at hcoreLe
  exact le_bot_iff.mp (hPcore.trans hcoreLe)

theorem rhoLin_apply_eq_self_of_mem_Rbar_of_le_centralizer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {Y : Subgroup (Hbar z)} (hY : ⁅Y, Y⁆ = Y)
    (hYC : Y ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z))) {r : Hbar z}
    (hr : r ∈ Rbar S a) :
    ∀ y ∈ Y, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v := by
  intro y hy v hv
  by_cases hr1 : r = 1
  · rw [hr1] at hv
    have hbot : commSpace (rhoLin S (1 : Hbar z)) = ⊥ := by
      rw [show rhoLin S (1 : Hbar z) = 1 from by simp [rhoLin]]
      exact CFSG.LargeExtraspecial.OrthoF2.commSpace_one
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv]
    simp
  · have hrA2 : r ∈ A2set S :=
      Tset_subset_A2set S a (h.mem_Tset_of_mem_Rbar hr hr1)
    exact rhoLin_apply_eq_self_of_perfect S hY hrA2
      (fun z hz => (Subgroup.mem_centralizer_iff.mp (hYC hz) r (h.Rbar_le_Xsub hr)).symm)
      y hy v hv

theorem aVec_not_mem_iSup_commSpace_of_le_centralizer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {Y : Subgroup (Hbar z)} (hY : ⁅Y, Y⁆ = Y)
    (hYC : Y ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z))) :
    aVec S h.mem_Q ∉ ⨆ y ∈ Y, commSpace (rhoLin S y) := by
  have hcommX : ∀ y ∈ Y, ∀ x : Hbar z, x ∈ Xsub S a → y * x = x * y := by
    intro y hy x hx
    exact (Subgroup.mem_centralizer_iff.mp (hYC hy) x hx).symm
  obtain ⟨r, hrR, hr1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Rbar S a)).resolve_left h.Rbar_ne_bot
  have hrT : r ∈ Tset S a := h.mem_Tset_of_mem_Rbar hrR hr1
  obtain ⟨e, heE, h3re⟩ := exists_mem_Eset_orderOf_mul_eq_three S a (Tset_subset_Eset S a hrT)
  have hrA2 : r ∈ A2set S := Tset_subset_A2set S a hrT
  have heA2 : e ∈ A2set S := Eset_subset_A2set S a heE
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have htypeR : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S r) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S hrA2
  have htypeE : CFSG.LargeExtraspecial.IsTypeA (qS S) (rhoLin S e) 2 :=
    isTypeA_rhoBar_of_isA2Hbar S heA2
  have h3lin : orderOf (rhoLin S r * rhoLin S e) = 3 := by
    rw [← rhoLin_mul, orderOf_rhoLin, h3re]
  have hmul := CFSG.LargeExtraspecial.commSpace_mul_of_orderOf_eq_three
    (q := qS S) (hq := by letI := modAbF S; exact q_nondegenerate S) htypeR htypeE h3lin
  have haR : aVec S h.mem_Q ∈ commSpace (rhoLin S r) :=
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hrR hr1
  have haω : aVec S h.mem_Q ∈ commSpace (rhoLin S (r * e)) := by
    rw [rhoLin_mul, hmul.2.1]
    exact Submodule.mem_sup_left haR
  have h4 := rhoLin_apply_eq_self_of_mem_Rbar_of_le_centralizer S h hY hYC hrR
  have heY : ∀ y ∈ Y, ∀ v ∈ commSpace (rhoLin S e), rhoLin S y v = v :=
    rhoLin_apply_eq_self_of_perfect S hY heA2
      (fun z hz => hcommX z hz e (subset_Xsub S a heE))
  have htriv : ∀ y ∈ Y, ∀ v ∈ commSpace (rhoLin S (r * e)), rhoLin S y v = v := by
    intro y hy v hv
    rw [rhoLin_mul, hmul.2.1, Submodule.mem_sup] at hv
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := hv
    rw [map_add, h4 y hy v1 hv1, heY y hy v2 hv2]
  exact aVec_not_mem_iSup_commSpace_of_trivial S h h3re haω htriv

theorem eq_bot_of_perfect_of_le_centralizer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {Y : Subgroup (Hbar z)} (hYn : Y.Normal) (hY : ⁅Y, Y⁆ = Y)
    (hYC : Y ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z))) : Y = ⊥ := by
  haveI hXn : (Xsub S a).Normal := Xsub_normal S a
  have hYoc : CFSG.GroupTheory.oddOrderClosure Y = Y :=
    CFSG.GroupTheory.oddOrderClosure_eq_self_of_commutator_eq hY
  have h2 : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥ :=
    fun P hPY hP2 hnorm => eq_bot_of_le_normalizer_of_isPGroup_two S hYn hPY hP2 hnorm
  have h3 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y := by
    intro y hy r hr
    exact (Subgroup.mem_centralizer_iff.mp (hYC hy) r (h.Rbar_le_Xsub hr)).symm
  have h4 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v :=
    fun y hy r hr => rhoLin_apply_eq_self_of_mem_Rbar_of_le_centralizer S h hY hYC hr y hy
  have h5 : aVec S h.mem_Q ∉ ⨆ y ∈ Y, commSpace (rhoLin S y) :=
    aVec_not_mem_iSup_commSpace_of_le_centralizer S h hY hYC
  have hLnorm : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) := by
    haveI : Y.Normal := hYn
    rw [Subgroup.normalizer_eq_top Y]
    exact le_top
  rcases h217 Y hYoc h2 h3 h4 h5 hLnorm with hR | hYbot
  · exact absurd hR h.Rbar_ne_bot
  · exact hYbot

theorem card_fittingSubgroup_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card (CFSG.fittingSubgroup
        (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 1 ∨
      Nat.card (CFSG.fittingSubgroup
        (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 3 := by
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  let Fc : Subgroup ↥C := CFSG.fittingSubgroup C
  let R : Subgroup (Hbar z) := Fc.map C.subtype
  haveI hXn : (Xsub S a).Normal := Xsub_normal S a
  haveI hCn : C.Normal := Subgroup.normal_centralizer
  have hRn : R.Normal := ConjAct.normal_of_characteristic_of_normal (H := C) (K := Fc)
  have hcard : Nat.card R = Nat.card Fc :=
    Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective
  haveI : R.Normal := hRn
  haveI : Group.IsNilpotent ↥R :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective Fc C.subtype C.subtype_injective)
  have hRodd : Odd (Nat.card R) :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.OddActorSylowFactorization.odd_of_pCore_bot
      (pCore_two_Hbar_eq_bot S) R
  have hRle : Nat.card R ≤ 3 := card_le_three_of_odd S h h217 hRodd (by
    haveI : R.Normal := hRn
    rw [Subgroup.normalizer_eq_top R]
    exact le_top)
  have hle3 : Nat.card Fc ≤ 3 := by rwa [hcard] at hRle
  have hoddF : Odd (Nat.card Fc) := by rwa [hcard] at hRodd
  obtain ⟨k, hk⟩ := hoddF
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with rfl | rfl
  · left; omega
  · right; omega

theorem fStar_centralizer_Xsub_eq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    fStar (Subgroup.centralizer (Xsub S a : Set (Hbar z))) =
      (CFSG.fittingSubgroup
        (Subgroup.centralizer (Xsub S a : Set (Hbar z)))).map
        (Subgroup.centralizer (Xsub S a : Set (Hbar z))).subtype := by
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  let Y : Subgroup (Hbar z) := (CFSG.layer C).map C.subtype
  have hYbot : Y = ⊥ := by
    have hY : ⁅Y, Y⁆ = Y := by
      change ⁅(CFSG.layer C).map C.subtype, (CFSG.layer C).map C.subtype⁆ =
        (CFSG.layer C).map C.subtype
      rw [← Subgroup.map_commutator (f := C.subtype), CFSG.LocalCores.layer_perfect]
    have hYn : Y.Normal := by
      haveI hXn : (Xsub S a).Normal := Xsub_normal S a
      haveI hCn : C.Normal := Subgroup.normal_centralizer
      haveI hYc : (CFSG.layer C).Characteristic := CFSG.LocalCores.layer_characteristic
      exact ConjAct.normal_of_characteristic_of_normal (H := C) (K := CFSG.layer C)
    have hYC : Y ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z)) :=
      Subgroup.map_subtype_le (CFSG.layer C)
    exact eq_bot_of_perfect_of_le_centralizer S h h217 hYn hY hYC
  change (CFSG.generalizedFitting C).map C.subtype =
    (CFSG.fittingSubgroup C).map C.subtype
  have hYbot' : (CFSG.layer C).map C.subtype = ⊥ := hYbot
  rw [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup, hYbot', sup_bot_eq]

theorem stroth78_33 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card (fStar (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 1 ∨
      Nat.card (fStar (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 3 := by
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have hF := card_fittingSubgroup_centralizer_Xsub S h h217
  have hE := fStar_centralizer_Xsub_eq S h h217
  rw [hE]
  rw [Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective]
  exact hF

theorem card_generalizedFitting_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card (CFSG.generalizedFitting
        (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 1 ∨
      Nat.card (CFSG.generalizedFitting
        (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) = 3 := by
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  have h33 := stroth78_33 S h h217
  have hcardmap : Nat.card (fStar C) = Nat.card (CFSG.generalizedFitting ↥C) :=
    Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective
  rw [hcardmap] at h33
  simpa [C] using h33

theorem card_centralizer_Xsub_dvd_six (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z))) ∣ 6 := by
  exact CFSG.GroupTheory.card_dvd_six_of_card_generalizedFitting
    (card_generalizedFitting_centralizer_Xsub S h h217)

theorem nonempty_mulEquiv_perm_three_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (heven : Even (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z))))) :
    Nonempty (Subgroup.centralizer (Xsub S a : Set (Hbar z)) ≃* Equiv.Perm (Fin 3)) := by
  exact CFSG.GroupTheory.nonempty_mulEquiv_perm_three_of_card_generalizedFitting
    (card_generalizedFitting_centralizer_Xsub S h h217) heven

end CFSG.RankThree.GF2n.Stroth78
