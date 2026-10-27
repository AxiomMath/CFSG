module

public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound

import CFSG.GroupTheory.InvertedNormalizedCyclic
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.RankThree.GF2n.Stroth78.Sec3FixedVector
import CFSG.RankThree.GF2n.Stroth78.Sec3Single
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_inverted_of_mem_Rbar_of_odd (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    {r x : Hbar z} (hr : r ∈ Rbar S a) (hx : x ∈ R) (hne : r * x ≠ x * r) :
    ∃ y ∈ R, y ≠ 1 ∧ r * y * r⁻¹ = y⁻¹ ∧
      ∀ ℓ ∈ Lbar S a, ℓ * y * ℓ⁻¹ = y ∨ ℓ * y * ℓ⁻¹ = y⁻¹ := by
  have hconjne : r * x * r⁻¹ ≠ x := by
    intro hc
    apply hne
    have h := congrArg (fun t => t * r) hc
    simpa [mul_assoc] using h
  have hLc : ∀ ℓ ∈ Lbar S a, ∀ m ∈ Lbar S a, ℓ * m = m * ℓ :=
    fun ℓ hℓ m hm => commute_of_mem_Lbar S h.mem_Q h.isConj hℓ hm
  have hL2 : ∀ ℓ ∈ Lbar S a, ℓ * ℓ = 1 :=
    fun ℓ hℓ => by
      rw [← pow_two]
      exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj hℓ
  exact CFSG.GroupTheory.exists_inverted_of_conj_ne (R := R) (L := Lbar S a)
    hR hLR hLc hL2 (Rbar_le_Lbar S a hr) hx hconjne

theorem exists_mem_Eset_mul_eq_of_conj_eq_inv (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    {r y : Hbar z} (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) (hyR : y ∈ R) (hy1 : y ≠ 1)
    (hyinv : r * y * r⁻¹ = y⁻¹) :
    ∃ e ∈ Eset S a, r * e = y ∧ orderOf (r * e) = 3 := by
  have hyordodd : Odd (orderOf y) := hR.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hyR)
  have hr2 : r * r = 1 := by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hr)
  let e : Hbar z := y * r * y⁻¹
  have heE : e ∈ Eset S a :=
    Eset_conj_mem S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hr hr1)) y
  have hre : r * e = y⁻¹ * y⁻¹ := by
    have hry : r * y = y⁻¹ * r := by
      have h := congrArg (fun t => t * r) hyinv
      simpa [mul_assoc] using h
    calc r * e = (r * y) * r * y⁻¹ := by dsimp [e]; group
      _ = (y⁻¹ * r) * r * y⁻¹ := by rw [hry]
      _ = y⁻¹ * (r * r) * y⁻¹ := by group
      _ = y⁻¹ * y⁻¹ := by rw [hr2, mul_one]
  have hord : orderOf (y⁻¹ * y⁻¹) = orderOf y := by
    rw [← mul_inv_rev y y, orderOf_inv]
    rw [show y * y = y ^ 2 from (pow_two y).symm, orderOf_pow,
      hyordodd.coprime_two_right.gcd_eq_one, Nat.div_one]
  have h3 : orderOf (r * e) = 3 := by
    have hodd : Odd (orderOf (r * e)) := by
      rw [hre, hord]
      exact hyordodd
    have hle4 : orderOf (r * e) ≤ 4 :=
      orderOf_mul_le_four_of_mem_Eset S a
        (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hr hr1)) heE
    have hne1 : orderOf (r * e) ≠ 1 := by
      rw [hre, hord]
      exact fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨k, hk⟩ := hodd
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      apply hne1
      omega
    have hk1 : k = 1 := by omega
    omega
  have hyinv2 : y⁻¹ * y⁻¹ = y := by
    have hy3 : y ^ 3 = 1 := by
      rw [show y ^ 3 = y ^ orderOf y from by rw [show orderOf y = 3 by
        rw [← hord, ← hre]; exact h3]]
      exact pow_orderOf_eq_one y
    have h2 : y ^ 2 = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc y ^ 2 * y = y ^ 3 := (pow_succ y 2).symm
        _ = 1 := hy3
    calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := (mul_inv_rev y y).symm
      _ = (y ^ 2)⁻¹ := by rw [pow_two]
      _ = y := by rw [h2, inv_inv]
  exact ⟨e, heE, hre.trans hyinv2, h3⟩

theorem commute_of_mem_Rbar_of_odd (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    {r x : Hbar z} (hr : r ∈ Rbar S a) (hx : x ∈ R) : r * x = x * r := by
  classical
  by_contra hne
  have hr1 : r ≠ 1 := by
    intro h1
    apply hne
    rw [h1]
    simp
  obtain ⟨y, hyR, hy1, hyinv, hyall⟩ :=
    exists_inverted_of_mem_Rbar_of_odd S h hR hLR hr hx hne
  obtain ⟨e, heE, hre, h3⟩ :=
    exists_mem_Eset_mul_eq_of_conj_eq_inv S h hR hr hr1 hyR hy1 hyinv
  obtain ⟨ℓ, hℓ, hℓne1, hℓne2⟩ :=
    exists_mem_Lbar_conj_ne_of_mem_Rbar S h hr hr1 heE h3
  rcases hyall ℓ hℓ with hfix | hinv
  · refine hℓne1 ?_
    calc ℓ * (r * e) * ℓ⁻¹ = ℓ * y * ℓ⁻¹ := by rw [hre]
      _ = y := hfix
      _ = r * e := hre.symm
  · refine hℓne2 ?_
    calc ℓ * (r * e) * ℓ⁻¹ = ℓ * y * ℓ⁻¹ := by rw [hre]
      _ = y⁻¹ := hinv
      _ = (r * e)⁻¹ := by rw [hre]

theorem odd_card_inf_commSpaceFixer (S : Setting z E F) (R : Subgroup (Hbar z)) (r : Hbar z)
    (hR : Odd (Nat.card R)) :
    Odd (Nat.card (R ⊓ commSpaceFixer S r : Subgroup (Hbar z))) :=
  hR.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem commute_inf_commSpaceFixer (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    (r : Hbar z) {r' : Hbar z} (hr : r ∈ Rbar S a) (hr' : r' ∈ Rbar S a)
    {y : Hbar z} (hy : y ∈ R ⊓ commSpaceFixer S r) : y * r' = r' * y :=
  (commute_of_mem_Rbar_of_odd S h hR hLR hr' hy.1).symm

theorem inf_commSpaceFixer_apply_eq_self (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    (r : Hbar z) (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) {r' : Hbar z}
    (hr' : r' ∈ Rbar S a) {y : Hbar z} (hy : y ∈ R ⊓ commSpaceFixer S r) :
    ∀ v ∈ commSpace (rhoLin S r'), rhoLin S y v = v := by
  have hyR : y ∈ R := hy.1
  have hya : rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q :=
    (mem_commSpaceFixer S r).mp hy.2 _ <|
      aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q hr hr1
  exact rhoLin_apply_eq_self_of_odd_of_commute S h hr'
    (commute_inf_commSpaceFixer S h hR hLR r hr hr' hy)
    (hR.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hyR)) hya

theorem aVec_not_mem_iSup_commSpace_inf_commSpaceFixer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (r : Hbar z) (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) :
    aVec S h.mem_Q ∉ ⨆ y ∈ R ⊓ commSpaceFixer S r, commSpace (rhoLin S y) := by
  refine aVec_not_mem_iSup_commSpace_of_odd S h (odd_card_inf_commSpaceFixer S R r hR) ?_
  intro y hy
  exact (mem_commSpaceFixer S r).mp hy.2 _ <|
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hr hr1

theorem normalizer_inf_commSpaceFixer (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)}
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    (r : Hbar z) (hr : r ∈ Rbar S a) :
    Lbar S a ≤ Subgroup.normalizer (R ⊓ commSpaceFixer S r : Set (Hbar z)) := by
  have hstep : ∀ ℓ ∈ Lbar S a, ∀ y : Hbar z, y ∈ R ⊓ commSpaceFixer S r →
      ℓ * y * ℓ⁻¹ ∈ R ⊓ commSpaceFixer S r := by
    intro ℓ hℓ y hy
    have hℓr : ℓ * r = r * ℓ :=
      commute_of_mem_Lbar S h.mem_Q h.isConj hℓ (Rbar_le_Lbar S a hr)
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hLR hℓ) y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_commSpaceFixer S hℓr) y).mp hy.2⟩
  intro ℓ hℓ
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hstep ℓ hℓ y, ?_⟩
  intro hy
  have h := hstep ℓ⁻¹ ((Lbar S a).inv_mem hℓ) (ℓ * y * ℓ⁻¹) hy
  simpa [mul_assoc] using h

theorem inf_commSpaceFixer_eq_bot (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    (r : Hbar z) (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) :
    R ⊓ commSpaceFixer S r = ⊥ :=
  (h217 (R ⊓ commSpaceFixer S r)
    (CFSG.GroupTheory.oddOrderClosure_eq_self_of_odd_card _
      (odd_card_inf_commSpaceFixer S R r hR))
    (fun P hPY hP2 _ => by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Disjoint.eq_bot_of_le
        (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup
          (odd_card_inf_commSpaceFixer S R r hR).not_two_dvd_nat hP2).symm hPY)
    (fun y hy r' hr' => commute_inf_commSpaceFixer S h hR hLR r hr hr' hy)
    (fun y hy r' hr' v hv =>
      inf_commSpaceFixer_apply_eq_self S h hR hLR r hr hr1 hr' hy v hv)
    (aVec_not_mem_iSup_commSpace_inf_commSpaceFixer S h hR r hr hr1)
    (normalizer_inf_commSpaceFixer S h hLR r hr)).resolve_left h.Rbar_ne_bot

theorem eq_of_apply_aVec_eq_of_inf_commSpaceFixer_eq_bot (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)))
    {r : Hbar z} (hr : r ∈ Rbar S a) (hr1 : r ≠ 1)
    (hYbot : R ⊓ commSpaceFixer S r = ⊥) {y y' : R}
    (hval : rhoLin S (y : Hbar z) (aVec S h.mem_Q) =
      rhoLin S (y' : Hbar z) (aVec S h.mem_Q)) : y = y' := by
  have hfix : rhoLin S ((y : Hbar z)⁻¹ * (y' : Hbar z)) (aVec S h.mem_Q) =
      aVec S h.mem_Q := by
    rw [rhoLin_mul, rhoLin_inv, LinearEquiv.mul_apply, ← hval]
    simp
  have hy'R : (y : Hbar z)⁻¹ * (y' : Hbar z) ∈ R :=
    R.mul_mem (R.inv_mem y.2) y'.2
  have hyr : ((y : Hbar z)⁻¹ * (y' : Hbar z)) * r =
      r * ((y : Hbar z)⁻¹ * (y' : Hbar z)) :=
    (commute_of_mem_Rbar_of_odd S h hR hLR hr hy'R).symm
  have htriv : ∀ v ∈ commSpace (rhoLin S r),
      rhoLin S ((y : Hbar z)⁻¹ * (y' : Hbar z)) v = v :=
    rhoLin_apply_eq_self_of_odd_of_commute S h hr hyr
      (hR.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hy'R)) hfix
  have hmemY : (y : Hbar z)⁻¹ * (y' : Hbar z) ∈ R ⊓ commSpaceFixer S r :=
    ⟨hy'R, (mem_commSpaceFixer S r).mpr htriv⟩
  have h1 : (y : Hbar z)⁻¹ * (y' : Hbar z) = 1 := by
    rw [hYbot] at hmemY
    simpa using hmemY
  have h2 : (y' : Hbar z) = (y : Hbar z) := by
    calc (y' : Hbar z) = (y : Hbar z) * ((y : Hbar z)⁻¹ * (y' : Hbar z)) := by group
      _ = (y : Hbar z) := by rw [h1, mul_one]
  exact Subtype.ext h2.symm

theorem card_le_three_of_odd (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {R : Subgroup (Hbar z)} (hR : Odd (Nat.card R))
    (hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z))) : Nat.card R ≤ 3 := by
  classical
  obtain ⟨r, hrR, hr1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Rbar S a)).resolve_left h.Rbar_ne_bot
  let W : Submodule (ZMod 2) (Additive (QbarOf S)) := commSpace (rhoLin S r)
  have hYbot : R ⊓ commSpaceFixer S r = ⊥ :=
    inf_commSpaceFixer_eq_bot S h h217 hR hLR r hrR hr1
  have haW : aVec S h.mem_Q ∈ W :=
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hrR hr1
  have hmemW : ∀ y : R, rhoLin S (y : Hbar z) (aVec S h.mem_Q) ∈ W := by
    intro y
    exact rhoLin_mem_commSpace_of_commute S
      (commute_of_mem_Rbar_of_odd S h hR hLR hrR y.2).symm haW
  have hneW : ∀ y : R,
      (⟨rhoLin S (y : Hbar z) (aVec S h.mem_Q), hmemW y⟩ : W) ≠ 0 := by
    intro y h0
    have hamb : rhoLin S (y : Hbar z) (aVec S h.mem_Q) ≠ 0 := by
      intro h1
      exact aV_ne_zero S h.mem_Q h.not_mem_ZQ
        ((LinearEquiv.map_eq_zero_iff (rhoLin S (y : Hbar z))).mp h1)
    exact hamb (congrArg Subtype.val h0)
  let f : R → {v : W // v ≠ 0} := fun y =>
    ⟨⟨rhoLin S (y : Hbar z) (aVec S h.mem_Q), hmemW y⟩, hneW y⟩
  have hinj : Function.Injective f := by
    intro y y' hyy'
    have h1 : (f y : W) = (f y' : W) := congrArg Subtype.val hyy'
    exact eq_of_apply_aVec_eq_of_inf_commSpaceFixer_eq_bot S h hR hLR hrR hr1 hYbot
      (congrArg Subtype.val h1)
  have hcardR : Nat.card R ≤ Nat.card {v : W // v ≠ 0} :=
    Nat.card_le_card_of_injective f hinj
  have hW2 : finrank (ZMod 2) W = 2 := by
    simpa [W, rhoLin] using
      (isTypeA_rhoBar_of_isA2Hbar S
        (isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
          h.centerIn_Qa_not_le_Q r hrR hr1)).2.2.2.1
  have hcardW : Nat.card W = 4 := by
    haveI : Finite (Additive (QbarOf S)) := inferInstance
    haveI : Finite W :=
      Finite.of_injective (fun v : W => (v : Additive (QbarOf S))) Subtype.coe_injective
    haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), hW2, Nat.card_zmod]
    norm_num
  have hcard : Nat.card {v : W // v ≠ 0} = 3 := by
    haveI : Finite (Additive (QbarOf S)) := inferInstance
    haveI : Finite W :=
      Finite.of_injective (fun v : W => (v : Additive (QbarOf S))) Subtype.coe_injective
    haveI : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card]
    have h' : Fintype.card {v : W // v ≠ 0} = Fintype.card W - 1 := by
      simpa using (Set.card_ne_eq (0 : W))
    rw [h']
    have hW4 : Fintype.card W = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcardW
    rw [hW4]
  omega

end CFSG.RankThree.GF2n.Stroth78
