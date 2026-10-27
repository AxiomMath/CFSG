module

public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.LocalData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.GroupTheory.QuaternionAutPrime

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open QuaternionGroup

local notation "P45" => Equiv.Perm (Fin 45)

private theorem c_alpha1_beta2 : alpha1 * beta2 = beta2 * alpha1 := by decide +kernel
private theorem c_beta1_alpha2 : beta1 * alpha2 = alpha2 * beta1 := by decide +kernel
private theorem s1_alpha1 : sigma1 * alpha1 * sigma1⁻¹ = beta1 := by decide +kernel
private theorem s1_alpha2 : sigma1 * alpha2 * sigma1⁻¹ = alpha2 := by decide +kernel
private theorem s1_beta2 : sigma1 * beta2 * sigma1⁻¹ = beta2 := by decide +kernel
private theorem s2_alpha1 : sigma2 * alpha1 * sigma2⁻¹ = alpha1 := by decide +kernel
private theorem s2_beta1 : sigma2 * beta1 * sigma2⁻¹ = beta1 := by decide +kernel
private theorem s2_alpha2 : sigma2 * alpha2 * sigma2⁻¹ = beta2 := by decide +kernel
private theorem sigma1_ne_sigma2' : sigma1 ≠ sigma2 := by decide +kernel
private theorem sigma1_ne_sigma2_inv : sigma1 ≠ sigma2⁻¹ := by decide +kernel

private def q8Theta : QuaternionGroup 2 →* QuaternionGroup 2 :=
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift (x := xa 0) (y := xa 1)
    (by decide) (by decide) (by decide)

private theorem q8Theta_a_one : q8Theta (a 1) = xa 0 := by decide

private theorem q8Theta_xa_zero : q8Theta (xa 0) = xa 1 := by decide

private theorem q8_exists_conj_theta {h : QuaternionGroup 2} (hh : h * h = a 2) :
    ∃ q : QuaternionGroup 2, q * h * q⁻¹ = a 1 ∨ q * q8Theta h * q⁻¹ = a 1 ∨
      q * q8Theta (q8Theta h) * q⁻¹ = a 1 := by
  revert h
  decide

private theorem q8_center {h : QuaternionGroup 2} (hh : ∀ k : QuaternionGroup 2, h * k = k * h) :
    h = 1 ∨ h = a 2 := by
  have h1 := hh (a 1)
  have h2 := hh (xa 0)
  revert h1 h2
  revert h
  decide

private theorem q8_sq_eq_one {h : QuaternionGroup 2} (hh : h * h = 1) : h = 1 ∨ h = a 2 := by
  revert h
  decide

private theorem q8_hom_ext {K : Type*} [Group K] {f g : QuaternionGroup 2 →* K}
    (h1 : f (a 1) = g (a 1)) (h2 : f (xa 0) = g (xa 0)) : f = g := by
  have ha : ∀ k : ZMod (2 * 2), f (a k) = g (a k) := by
    intro k
    rw [← ZMod.natCast_zmod_val k, ← QuaternionGroup.a_one_pow, map_pow, map_pow, h1]
  ext x
  rcases x with k | k
  · exact ha k
  · rw [show (xa k : QuaternionGroup 2) = xa 0 * a k by rw [QuaternionGroup.xa_mul_a, zero_add],
      map_mul, map_mul, h2, ha]

private theorem s1_beta1' : sigma1 * beta1 * sigma1⁻¹ = beta1 * alpha1 := by decide +kernel
private theorem s2_beta2' : sigma2 * beta2 * sigma2⁻¹ = beta2 * alpha2 := by decide +kernel
private theorem b1_a1_b1 : beta1 * alpha1 * beta1⁻¹ = alpha1⁻¹ := by decide +kernel
private theorem b2_a2_b2 : beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹ := by decide +kernel
private theorem sq_b1 : beta1 ^ 2 = alpha1 ^ 2 := by decide +kernel
private theorem sq_b2 : beta2 ^ 2 = alpha2 ^ 2 := by decide +kernel
private theorem sq_a1 : alpha1 ^ 2 = t := by decide +kernel
private theorem sq_a2 : alpha2 ^ 2 = t := by decide +kernel
private theorem p4_a1 : alpha1 ^ 4 = 1 := by decide +kernel
private theorem p4_a2 : alpha2 ^ 4 = 1 := by decide +kernel
private theorem v_ut : v * (u * t) = u * t * v := by decide +kernel
private theorem v_s1s2 : v * (sigma1 * sigma2) * v⁻¹ = (sigma1 * sigma2)⁻¹ := by decide +kernel
private theorem v_s1s2inv : v * (sigma1 * sigma2⁻¹) * v⁻¹ = (sigma1 * sigma2⁻¹)⁻¹ := by
  decide +kernel
private theorem uv_s1s2inv : u * v * (sigma1 * sigma2⁻¹) = sigma1 * sigma2⁻¹ * (u * v) := by
  decide +kernel
private theorem u_s1s2inv : u * (sigma1 * sigma2⁻¹) * u⁻¹ = (sigma1 * sigma2⁻¹)⁻¹ := by
  decide +kernel
private theorem s1_u_comm : sigma1 * u * sigma1⁻¹ * u⁻¹ = sigma1 * sigma2⁻¹ := by decide +kernel
private theorem s1s2inv_cube : (sigma1 * sigma2⁻¹) ^ 3 = 1 := by decide +kernel
private theorem s1s2inv_ne_one : sigma1 * sigma2⁻¹ ≠ 1 := by decide +kernel
private theorem t_ne_one' : t ≠ 1 := by decide +kernel

private theorem factorization_576 : (576 : ℕ).factorization 2 = 6 := by
  rw [show (576 : ℕ) = 2 ^ 6 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

private theorem card_centralizer_eq_of_map_conj {K : Type*} [Group K] [Finite K] {x y g : K}
    (h : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y) :
    Nat.card (Subgroup.centralizer ({x} : Set K)) =
      Nat.card (Subgroup.centralizer ({y} : Set K)) := by
  have hx : Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers y := by
    rw [← h, MonoidHom.map_zpowers]
    rfl
  have h1 : Subgroup.centralizer ({g * x * g⁻¹} : Set K) =
      Subgroup.centralizer ({y} : Set K) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hx,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← h1]
  exact CFSG.GroupTheory.card_centralizer_eq_of_isConj (isConj_iff.mpr ⟨g, rfl⟩)

private theorem map_centralizer_eq {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (x : K) :
    (Subgroup.centralizer ({x} : Set K)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set K') := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change e c * e x = e x * e c
    rw [← map_mul, hc', map_mul]
  · intro hg
    have hg' : g * e x = e x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine ⟨e.symm g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg']

private theorem map_inSubgroup_pCore_centralizer {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (x : K) :
    (inSubgroup (pCore 2) (Subgroup.centralizer ({x} : Set K))).map e.toMonoidHom =
      inSubgroup (pCore 2) (Subgroup.centralizer ({e x} : Set K')) := by
  set Cx := Subgroup.centralizer ({x} : Set K)
  set Cy := Subgroup.centralizer ({e x} : Set K')
  have hmap : Cx.map e.toMonoidHom = Cy := map_centralizer_eq e x
  let e' : ↥Cx ≃* ↥Cy :=
    (Subgroup.equivMapOfInjective Cx e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap)
  have hcomp : e.toMonoidHom.comp Cx.subtype = Cy.subtype.comp e'.toMonoidHom := by
    ext c
    rfl
  unfold inSubgroup
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso 2 e']

private theorem card_centralizer_map {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (x : K) :
    Nat.card (Subgroup.centralizer ({e x} : Set K')) =
      Nat.card (Subgroup.centralizer ({x} : Set K)) := by
  rw [← map_centralizer_eq e x, Subgroup.card_map_of_injective e.injective]

set_option quotPrecheck false in
local notation "P45Q" => ↥QP45.originalSubgroup
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tQ" => (⟨t, t_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "uQ" => (⟨u, u_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "s1Q" => (⟨sigma1, sigma1_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "s2Q" => (⟨sigma2, sigma2_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "a1Q" => (⟨alpha1, alpha1_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "b1Q" => (⟨beta1, beta1_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "a2Q" => (⟨alpha2, alpha2_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "b2Q" => (⟨beta2, beta2_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "bQ" => (⟨beta, beta_mem_Q⟩ : P45Q)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "Pp" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup

private noncomputable abbrev ιQ : P45Q →* A45 := Subgroup.inclusion QP45_le_QA45

private theorem ιQ_injective : Function.Injective ιQ := Subgroup.inclusion_injective _

private theorem ιQ_mem (x : P45Q) : ιQ x ∈ Pp := by
  rw [Subgroup.mem_subgroupOf]
  exact x.2

private theorem exists_ιQ_eq {g : A45} (hg : g ∈ Pp) : ∃ x : P45Q, ιQ x = g :=
  ⟨⟨g, Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩

private theorem vA_not_mem : vA ∉ Pp := by
  rw [Subgroup.mem_subgroupOf]
  exact v_not_mem_Q

private theorem mul_mem_of_not_mem {g w : A45} (hg : g ∉ Pp) (hw : w ∉ Pp) : w * g ∈ Pp := by
  rw [Subgroup.mul_mem_iff_of_index_two index_QP45]
  exact iff_of_false hw hg

private theorem uvA_not_mem : uA * vA ∉ Pp := by
  intro h
  rw [Subgroup.mul_mem_iff_of_index_two index_QP45] at h
  exact vA_not_mem (h.mp (ιQ_mem uQ))

private theorem Pp_normal : (Pp).Normal := Subgroup.normal_of_index_eq_two index_QP45

private theorem isConj_of_isConj_ιQ {x y : P45Q} {w : A45} (hw : w ∉ Pp)
    (hwx : w * ιQ x = ιQ x * w) (h : IsConj (ιQ y) (ιQ x)) : IsConj y x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  by_cases hcP : c ∈ Pp
  · obtain ⟨c', rfl⟩ := exists_ιQ_eq hcP
    exact isConj_iff.mpr ⟨c', ιQ_injective (by rw [map_mul, map_mul, map_inv]; exact hc)⟩
  · obtain ⟨c', hc'⟩ := exists_ιQ_eq (mul_mem_of_not_mem hcP hw)
    refine isConj_iff.mpr ⟨c', ιQ_injective ?_⟩
    rw [map_mul, map_mul, map_inv, hc']
    calc w * c * ιQ y * (w * c)⁻¹ = w * (c * ιQ y * c⁻¹) * w⁻¹ := by group
      _ = w * ιQ x * w⁻¹ := by rw [hc]
      _ = ιQ x := by rw [hwx, mul_inv_cancel_right]

private theorem two_mul_card_comap {K : Subgroup A45} {w : A45} (hwK : w ∈ K) (hw : w ∉ Pp) :
    2 * Nat.card ↥(K.comap ιQ) = Nat.card K := by
  have hmap : (K.comap ιQ).map ιQ = Pp ⊓ K := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨ιQ_mem c, hc⟩
    · rintro ⟨hgP, hgK⟩
      obtain ⟨c, rfl⟩ := exists_ιQ_eq hgP
      exact ⟨c, hgK, rfl⟩
  have hcard : Nat.card ↥(K.comap ιQ) = Nat.card ↥(Pp ⊓ K) := by
    rw [← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ ιQ_injective).toEquiv
  have hrel : (Pp).relIndex K = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨w, hwK, hw, fun b _ => ?_⟩
    by_cases hb : b ∈ Pp
    · exact Or.inr hb
    · left
      rw [Subgroup.mul_mem_iff_of_index_two index_QP45]
      exact iff_of_false hb hw
  rw [hcard, ← hrel, Subgroup.relIndex_mul_card]

private theorem comap_centralizer (x : P45Q) :
    (Subgroup.centralizer ({ιQ x} : Set A45)).comap ιQ = Subgroup.centralizer ({x} : Set P45Q) := by
  ext c
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ιQ_injective (by rw [map_mul, map_mul]; exact h)
  · intro h
    rw [← map_mul, h, map_mul]

private theorem two_mul_card_centralizer {x : P45Q} {w : A45} (hw : w ∉ Pp)
    (hwx : w * ιQ x = ιQ x * w) :
    2 * Nat.card (Subgroup.centralizer ({x} : Set P45Q)) =
      Nat.card (Subgroup.centralizer ({ιQ x} : Set A45)) := by
  rw [← comap_centralizer]
  exact two_mul_card_comap (Subgroup.mem_centralizer_singleton_iff.mpr hwx) hw

private theorem hvt : vA * ιQ tQ = ιQ tQ * vA := Subtype.ext t_commute_v.symm

private theorem hvut : vA * ιQ (uQ * tQ) = ιQ (uQ * tQ) * vA := Subtype.ext v_ut

theorem qp45_card_centralizer_t :
    Nat.card (Subgroup.centralizer ({tQ} : Set P45Q)) = 576 := by
  have h := two_mul_card_centralizer vA_not_mem hvt
  have hA : Nat.card (Subgroup.centralizer ({ιQ tQ} : Set A45)) = 1152 := by
    rw [show ιQ tQ = tA from rfl, card_centralizer_QA45_eq_filter t t_mem_A]
    exact Certificates.certificate946005.centralizer_t
  omega

theorem qp45_card_centralizer_ut :
    Nat.card (Subgroup.centralizer ({uQ * tQ} : Set P45Q)) = 96 := by
  have h := two_mul_card_centralizer vA_not_mem hvut
  have hA : Nat.card (Subgroup.centralizer ({ιQ (uQ * tQ)} : Set A45)) = 192 := by
    rw [show ιQ (uQ * tQ) = uA * tA from rfl]
    exact qa45_involution_centralizers.2.1
  omega

theorem qp45_involution_classes :
    ∀ x : P45Q, orderOf x = 2 → IsConj x tQ ∨ IsConj x (uQ * tQ) := by
  intro x hx
  have hxA : orderOf (ιQ x) = 2 := by
    rw [orderOf_injective ιQ ιQ_injective]
    exact hx
  have hnot : ∀ g : A45, g ∉ Pp → ¬ IsConj (ιQ x) g := by
    intro g hg hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact hg (hc ▸ Pp_normal.conj_mem _ (ιQ_mem x) c)
  rcases qa45_involution_classes (ιQ x) hxA with h | h | h | h
  · exact Or.inl (isConj_of_isConj_ιQ vA_not_mem hvt h)
  · exact Or.inr (isConj_of_isConj_ιQ vA_not_mem hvut h)
  · exact absurd h (hnot _ vA_not_mem)
  · exact absurd h (hnot _ uvA_not_mem)

theorem qp45_not_isConj_t_ut : ¬ IsConj tQ (uQ * tQ) := by
  intro h
  have h1 := CFSG.GroupTheory.card_centralizer_eq_of_isConj h
  rw [qp45_card_centralizer_t, qp45_card_centralizer_ut] at h1
  omega

private theorem map_ιQ_conj (Y : Subgroup P45Q) (g : P45Q) :
    (Y.map (MulAut.conj g).toMonoidHom).map ιQ =
      (Y.map ιQ).map (MulAut.conj (ιQ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem qp45_orderThree_subgroup_classes :
    ∀ Y : Subgroup P45Q, Nat.card Y = 3 →
      (∃ g : P45Q, Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers s1Q) ∨
      (∃ g : P45Q, Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (s1Q * s2Q)) ∨
      (∃ g : P45Q, Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (s1Q * s2Q⁻¹)) := by
  intro Y hY
  have hYA : Nat.card (Y.map ιQ) = 3 := by
    rw [Subgroup.card_map_of_injective ιQ_injective, hY]
  have hlift : ∀ x : P45Q, vA * ιQ x * vA⁻¹ = (ιQ x)⁻¹ →
      QA45SubgroupConj (Y.map ιQ) (Subgroup.zpowers (ιQ x)) →
      ∃ g : P45Q, Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
    intro x hvx hconj
    obtain ⟨g, hg⟩ := hconj
    have key : ∀ g' : A45, g' ∈ Pp →
        (Y.map ιQ).map (MulAut.conj g').toMonoidHom = Subgroup.zpowers (ιQ x) →
        ∃ c : P45Q, Y.map (MulAut.conj c).toMonoidHom = Subgroup.zpowers x := by
      intro g' hg'P hg'
      obtain ⟨c, rfl⟩ := exists_ιQ_eq hg'P
      refine ⟨c, Subgroup.map_injective ιQ_injective ?_⟩
      rw [map_ιQ_conj, hg', MonoidHom.map_zpowers]
    by_cases hgP : g ∈ Pp
    · exact key g hgP hg
    · refine key (vA * g) (mul_mem_of_not_mem hgP vA_not_mem) ?_
      have hcomp : (MulAut.conj (vA * g)).toMonoidHom =
          (MulAut.conj vA).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, ← Subgroup.map_map, hg, MonoidHom.map_zpowers]
      change Subgroup.zpowers (vA * ιQ x * vA⁻¹) = _
      rw [hvx, Subgroup.zpowers_inv]
  have hv1 : vA * ιQ s1Q * vA⁻¹ = (ιQ s1Q)⁻¹ := Subtype.ext sigma1_conj_v
  have hv2 : vA * ιQ (s1Q * s2Q) * vA⁻¹ = (ιQ (s1Q * s2Q))⁻¹ := Subtype.ext v_s1s2
  have hv3 : vA * ιQ (s1Q * s2Q⁻¹) * vA⁻¹ = (ιQ (s1Q * s2Q⁻¹))⁻¹ := Subtype.ext v_s1s2inv
  rcases qa45_orderThree_subgroup_classes (Y.map ιQ) hYA with h | h | h
  · exact Or.inl (hlift s1Q hv1 h)
  · exact Or.inr (Or.inl (hlift (s1Q * s2Q) hv2 h))
  · exact Or.inr (Or.inr (hlift (s1Q * s2Q⁻¹) hv3 h))

theorem qp45_orderThree_subgroup_not_conj :
    (¬ ∃ g : P45Q, (Subgroup.zpowers s1Q).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (s1Q * s2Q)) ∧
    (¬ ∃ g : P45Q, (Subgroup.zpowers s1Q).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (s1Q * s2Q⁻¹)) ∧
    (¬ ∃ g : P45Q, (Subgroup.zpowers (s1Q * s2Q)).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers (s1Q * s2Q⁻¹)) := by
  have hcard : ∀ x y : P45Q, (∃ g : P45Q, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers y) → Nat.card (Subgroup.centralizer ({ιQ x} : Set A45)) =
        Nat.card (Subgroup.centralizer ({ιQ y} : Set A45)) := by
    rintro x y ⟨g, hg⟩
    apply card_centralizer_eq_of_map_conj (g := ιQ g)
    have h := congrArg (Subgroup.map ιQ) hg
    rw [map_ιQ_conj, MonoidHom.map_zpowers ιQ x, MonoidHom.map_zpowers ιQ y] at h
    exact h
  have h1 : Nat.card (Subgroup.centralizer ({ιQ s1Q} : Set A45)) = 648 := by
    rw [show ιQ s1Q = ⟨sigma1, sigma1_mem_A⟩ from rfl, card_centralizer_QA45_eq_filter _ _]
    exact Certificates.certificate946005.centralizer_sigma1
  have h2 : Nat.card (Subgroup.centralizer ({ιQ (s1Q * s2Q)} : Set A45)) = 216 := by
    rw [show ιQ (s1Q * s2Q) = ⟨sigma1 * sigma2, QA45.originalSubgroup.mul_mem sigma1_mem_A
      sigma2_mem_A⟩ from rfl, card_centralizer_QA45_eq_filter _ _]
    exact Certificates.certificate946005.centralizer_sigma1sigma2
  have h3 : Nat.card (Subgroup.centralizer ({ιQ (s1Q * s2Q⁻¹)} : Set A45)) = 108 := by
    rw [show ιQ (s1Q * s2Q⁻¹) = ⟨sigma1 * sigma2⁻¹, QA45.originalSubgroup.mul_mem sigma1_mem_A
      (QA45.originalSubgroup.inv_mem sigma2_mem_A)⟩ from rfl, card_centralizer_QA45_eq_filter _ _]
    exact Certificates.certificate946005.centralizer_sigma1sigma2inv
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := hcard _ _ h
    omega
  · have := hcard _ _ h
    omega
  · have := hcard _ _ h
    omega

theorem qp45_card_centralizer_s1s2inv :
    Nat.card (Subgroup.centralizer ({s1Q * s2Q⁻¹} : Set P45Q)) = 54 := by
  have h := two_mul_card_centralizer (x := s1Q * s2Q⁻¹) uvA_not_mem (Subtype.ext uv_s1s2inv)
  have hA : Nat.card (Subgroup.centralizer ({ιQ (s1Q * s2Q⁻¹)} : Set A45)) = 108 := by
    rw [show ιQ (s1Q * s2Q⁻¹) = ⟨sigma1 * sigma2⁻¹, QA45.originalSubgroup.mul_mem sigma1_mem_A
      (QA45.originalSubgroup.inv_mem sigma2_mem_A)⟩ from rfl, card_centralizer_QA45_eq_filter _ _]
    exact Certificates.certificate946005.centralizer_sigma1sigma2inv
  omega

theorem qp45_u_inverts_s1s2inv : uQ * (s1Q * s2Q⁻¹) * uQ⁻¹ = (s1Q * s2Q⁻¹)⁻¹ :=
  Subtype.ext u_s1s2inv

set_option quotPrecheck false in
local notation "Qd" => Subgroup.closure ({a1Q, b1Q, a2Q, b2Q} : Set P45Q)

private theorem a1Q_pow4 : a1Q ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact p4_a1)
private theorem a2Q_pow4 : a2Q ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact p4_a2)
private theorem b1a1Q : b1Q * a1Q * b1Q⁻¹ = a1Q⁻¹ := Subtype.ext b1_a1_b1
private theorem b2a2Q : b2Q * a2Q * b2Q⁻¹ = a2Q⁻¹ := Subtype.ext b2_a2_b2
private theorem sqb1Q : b1Q ^ 2 = a1Q ^ 2 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow]; exact sq_b1)
private theorem sqb2Q : b2Q ^ 2 = a2Q ^ 2 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow]; exact sq_b2)

private def f1 : QuaternionGroup 2 →* P45Q :=
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift a1Q_pow4 b1a1Q sqb1Q

private def f2 : QuaternionGroup 2 →* P45Q :=
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift a2Q_pow4 b2a2Q sqb2Q

private theorem f1_a (k : ZMod (2 * 2)) : f1 (a k) = a1Q ^ k.val := rfl
private theorem f1_xa (k : ZMod (2 * 2)) : f1 (xa k) = b1Q * a1Q ^ k.val := rfl
private theorem f2_a (k : ZMod (2 * 2)) : f2 (a k) = a2Q ^ k.val := rfl
private theorem f2_xa (k : ZMod (2 * 2)) : f2 (xa k) = b2Q * a2Q ^ k.val := rfl

private theorem f1_a1 : f1 (a 1) = a1Q := by rw [f1_a]; exact pow_one _
private theorem f2_a1 : f2 (a 1) = a2Q := by rw [f2_a]; exact pow_one _
private theorem f1_xa0 : f1 (xa 0) = b1Q := by rw [f1_xa]; exact mul_one _
private theorem f2_xa0 : f2 (xa 0) = b2Q := by rw [f2_xa]; exact mul_one _
private theorem f1_xa1 : f1 (xa 1) = b1Q * a1Q := by
  rw [f1_xa, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
private theorem f2_xa1 : f2 (xa 1) = b2Q * a2Q := by
  rw [f2_xa, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
private theorem f1_a2 : f1 (a 2) = tQ := by
  rw [f1_a]
  exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact sq_a1)
private theorem f2_a2 : f2 (a 2) = tQ := by
  rw [f2_a]
  exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact sq_a2)

private theorem tQ_ne_one : tQ ≠ 1 := fun h => t_ne_one' (congrArg Subtype.val h)

private theorem f1_injective : Function.Injective f1 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := CFSG.GroupTheory.quaternion_a_two_mem_of_ne_bot hne
  rw [MonoidHom.mem_ker, f1_a2] at h
  exact tQ_ne_one h

private theorem f2_injective : Function.Injective f2 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := CFSG.GroupTheory.quaternion_a_two_mem_of_ne_bot hne
  rw [MonoidHom.mem_ker, f2_a2] at h
  exact tQ_ne_one h

private theorem commute_f1_f2 (h h' : QuaternionGroup 2) : Commute (f1 h) (f2 h') := by
  have c1 : Commute a1Q a2Q := Subtype.ext alpha1_commute_alpha2
  have c2 : Commute a1Q b2Q := Subtype.ext c_alpha1_beta2
  have c3 : Commute b1Q a2Q := Subtype.ext c_beta1_alpha2
  have c4 : Commute b1Q b2Q := Subtype.ext beta1_commute_beta2
  have hA : Commute a1Q (f2 h') := by
    rcases h' with k | k
    · rw [f2_a]; exact c1.pow_right _
    · rw [f2_xa]; exact c2.mul_right (c1.pow_right _)
  have hB : Commute b1Q (f2 h') := by
    rcases h' with k | k
    · rw [f2_a]; exact c3.pow_right _
    · rw [f2_xa]; exact c4.mul_right (c3.pow_right _)
  rcases h with k | k
  · rw [f1_a]; exact hA.pow_left _
  · rw [f1_xa]; exact hB.mul_left (hA.pow_left _)

private def fPhi : QuaternionGroup 2 × QuaternionGroup 2 →* P45Q :=
  f1.noncommCoprod f2 commute_f1_f2

private theorem fPhi_apply (h h' : QuaternionGroup 2) : fPhi (h, h') = f1 h * f2 h' := rfl

private theorem f1_mem_Qd (h : QuaternionGroup 2) : f1 h ∈ Qd := by
  have ha : a1Q ∈ Qd := Subgroup.subset_closure (by simp)
  have hb : b1Q ∈ Qd := Subgroup.subset_closure (by simp)
  rcases h with k | k
  · rw [f1_a]; exact Subgroup.pow_mem _ ha _
  · rw [f1_xa]; exact Subgroup.mul_mem _ hb (Subgroup.pow_mem _ ha _)

private theorem f2_mem_Qd (h : QuaternionGroup 2) : f2 h ∈ Qd := by
  have ha : a2Q ∈ Qd := Subgroup.subset_closure (by simp)
  have hb : b2Q ∈ Qd := Subgroup.subset_closure (by simp)
  rcases h with k | k
  · rw [f2_a]; exact Subgroup.pow_mem _ ha _
  · rw [f2_xa]; exact Subgroup.mul_mem _ hb (Subgroup.pow_mem _ ha _)

private theorem range_fPhi : fPhi.range = Qd := by
  apply le_antisymm
  · rintro _ ⟨⟨h, h'⟩, rfl⟩
    rw [fPhi_apply]
    exact Subgroup.mul_mem _ (f1_mem_Qd h) (f2_mem_Qd h')
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨(a 1, 1), by rw [fPhi_apply, f1_a1, map_one, mul_one]⟩
    · exact ⟨(xa 0, 1), by rw [fPhi_apply, f1_xa0, map_one, mul_one]⟩
    · exact ⟨(1, a 1), by rw [fPhi_apply, f2_a1, map_one, one_mul]⟩
    · exact ⟨(1, xa 0), by rw [fPhi_apply, f2_xa0, map_one, one_mul]⟩

private theorem map_Qd : (Qd).map ιQ = oTwoQA45 := by
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

private theorem card_Qd : Nat.card Qd = 32 := by
  rw [← Subgroup.card_map_of_injective ιQ_injective, map_Qd, card_oTwoQA45]
  norm_num

private theorem Qd_le_C : Qd ≤ Subgroup.centralizer ({tQ} : Set P45Q) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subtype.ext t_commute_alpha1.symm
  · exact Subtype.ext t_commute_beta1.symm
  · exact Subtype.ext t_commute_alpha2.symm
  · exact Subtype.ext t_commute_beta2.symm

private theorem sylowTwoQA45_le_centralizer_t :
    sylowTwoQA45 ≤ Subgroup.centralizer ({tA} : Set A45) := by
  rw [sylowTwoQA45, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subtype.ext t_commute_u.symm
  · exact Subtype.ext t_commute_v.symm
  · exact Subtype.ext t_commute_alpha1.symm
  · exact Subtype.ext t_commute_beta1.symm
  · exact Subtype.ext t_commute_alpha2.symm
  · exact Subtype.ext t_commute_beta2.symm

private theorem TP_le_C :
    sylowTwoQA45.comap ιQ ≤ Subgroup.centralizer ({tQ} : Set P45Q) := by
  rw [← comap_centralizer]
  exact Subgroup.comap_mono sylowTwoQA45_le_centralizer_t

private theorem TP_le_normalizer :
    sylowTwoQA45.comap ιQ ≤ Subgroup.normalizer (Qd : Set P45Q) := by
  intro x hx
  have hxN := sylowTwoQA45_le_normalizer_oTwoQA45 hx
  rw [Subgroup.mem_normalizer_iff] at hxN ⊢
  intro q
  have h1 : ιQ (x * q * x⁻¹) = ιQ x * ιQ q * (ιQ x)⁻¹ := by rw [map_mul, map_mul, map_inv]
  rw [← Subgroup.mem_map_iff_mem ιQ_injective (K := Qd), map_Qd, hxN, ← h1, ← map_Qd,
    Subgroup.mem_map_iff_mem ιQ_injective]

private theorem vA_mem_sylowTwo : vA ∈ sylowTwoQA45 := Subgroup.subset_closure (by simp)

private theorem card_TP : Nat.card ↥(sylowTwoQA45.comap ιQ) = 64 := by
  have h := two_mul_card_comap vA_mem_sylowTwo vA_not_mem
  rw [card_sylowTwoQA45] at h
  omega

private theorem isPGroup_TP : IsPGroup 2 ↥(sylowTwoQA45.comap ιQ) :=
  IsPGroup.of_card (n := 6) card_TP

private theorem mem_normalizer_Qd_of {g : P45Q}
    (hg : ∀ x ∈ ({a1Q, b1Q, a2Q, b2Q} : Set P45Q), g * x * g⁻¹ ∈ Qd) :
    g ∈ Subgroup.normalizer (Qd : Set P45Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Qd).map (MulAut.conj g).toMonoidHom ≤ Qd := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

private theorem s1Q_mem_normalizer : s1Q ∈ Subgroup.normalizer (Qd : Set P45Q) := by
  apply mem_normalizer_Qd_of
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [show s1Q * a1Q * s1Q⁻¹ = b1Q from Subtype.ext s1_alpha1]
    exact Subgroup.subset_closure (by simp)
  · rw [show s1Q * b1Q * s1Q⁻¹ = b1Q * a1Q from Subtype.ext s1_beta1']
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [show s1Q * a2Q * s1Q⁻¹ = a2Q from Subtype.ext s1_alpha2]
    exact Subgroup.subset_closure (by simp)
  · rw [show s1Q * b2Q * s1Q⁻¹ = b2Q from Subtype.ext s1_beta2]
    exact Subgroup.subset_closure (by simp)

private theorem s2Q_mem_normalizer : s2Q ∈ Subgroup.normalizer (Qd : Set P45Q) := by
  apply mem_normalizer_Qd_of
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [show s2Q * a1Q * s2Q⁻¹ = a1Q from Subtype.ext s2_alpha1]
    exact Subgroup.subset_closure (by simp)
  · rw [show s2Q * b1Q * s2Q⁻¹ = b1Q from Subtype.ext s2_beta1]
    exact Subgroup.subset_closure (by simp)
  · rw [show s2Q * a2Q * s2Q⁻¹ = b2Q from Subtype.ext s2_alpha2]
    exact Subgroup.subset_closure (by simp)
  · rw [show s2Q * b2Q * s2Q⁻¹ = b2Q * a2Q from Subtype.ext s2_beta2']
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private theorem s1Q_mem_C : s1Q ∈ Subgroup.centralizer ({tQ} : Set P45Q) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_sigma1.symm)

private theorem s2Q_mem_C : s2Q ∈ Subgroup.centralizer ({tQ} : Set P45Q) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_sigma2.symm)

private theorem orderOf_s1Q : orderOf s1Q = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime sigma1_cube sigma1_ne_one

private theorem orderOf_s2Q : orderOf s2Q = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime sigma2_cube sigma2_ne_one

private theorem zpowers_s1Q_inf_s2Q : Subgroup.zpowers s1Q ⊓ Subgroup.zpowers s2Q = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Subgroup.zpowers s1Q) = 3 := by rw [Nat.card_zpowers, orderOf_s1Q]
  have hle : Subgroup.zpowers s1Q ⊓ Subgroup.zpowers s2Q ≤ Subgroup.zpowers s1Q := inf_le_left
  have hfact : Fact (Nat.card ↥(Subgroup.zpowers s1Q)).Prime :=
    ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers s1Q ⊓ Subgroup.zpowers s2Q).subgroupOf (Subgroup.zpowers s1Q)) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hle
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    have hs1 : s1Q ∈ Subgroup.zpowers s2Q := (h (Subgroup.mem_zpowers s1Q)).2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs1
    rw [← zpow_mod_orderOf, orderOf_s2Q] at hk
    have hk3 : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · rw [h0, zpow_zero] at hk
      exact sigma1_ne_one (congrArg Subtype.val hk).symm
    · rw [h1, zpow_one] at hk
      exact sigma1_ne_sigma2' (congrArg Subtype.val hk).symm
    · rw [h2] at hk
      have h3 : s2Q ^ (2 : ℤ) = s2Q⁻¹ := by
        rw [zpow_two, ← mul_eq_one_iff_eq_inv, ← pow_three', ← orderOf_s2Q, pow_orderOf_eq_one]
      rw [h3] at hk
      exact sigma1_ne_sigma2_inv (congrArg Subtype.val hk).symm

private theorem nine_dvd_card_of_le {N : Subgroup P45Q} (h1 : s1Q ∈ N) (h2 : s2Q ∈ N) :
    9 ∣ Nat.card N := by
  have hcomm : ∀ (x : Subgroup.zpowers s1Q) (y : Subgroup.zpowers s2Q),
      Commute ((Subgroup.zpowers s1Q).subtype x) ((Subgroup.zpowers s2Q).subtype y) := by
    intro x y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change Commute (x : P45Q) (y : P45Q)
    rw [← hi, ← hj]
    have hc : Commute s1Q s2Q := by
      rw [commute_iff_eq]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact sigma1_commute_sigma2
    exact hc.zpow_zpow i j
  let Ψ := (Subgroup.zpowers s1Q).subtype.noncommCoprod (Subgroup.zpowers s2Q).subtype hcomm
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hxy
    have hxy' : (x : P45Q) = (y : P45Q)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hmem : (x : P45Q) ∈ Subgroup.zpowers s1Q ⊓ Subgroup.zpowers s2Q :=
      ⟨x.2, hxy' ▸ Subgroup.inv_mem _ y.2⟩
    rw [zpowers_s1Q_inf_s2Q, Subgroup.mem_bot] at hmem
    have hy1 : (y : P45Q) = 1 := by rw [hmem, eq_comm, inv_eq_one] at hxy'; exact hxy'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy1)
  have hle : Ψ.range ≤ N := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [MonoidHom.noncommCoprod_apply]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change (x : P45Q) * (y : P45Q) ∈ N
    rw [← hi, ← hj]
    exact N.mul_mem (N.zpow_mem h1 i) (N.zpow_mem h2 j)
  have hcard : Nat.card Ψ.range = 9 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, orderOf_s1Q, orderOf_s2Q]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

private theorem C_le_normalizer_Qd :
    Subgroup.centralizer ({tQ} : Set P45Q) ≤ Subgroup.normalizer (Qd : Set P45Q) := by
  set C := Subgroup.centralizer ({tQ} : Set P45Q)
  set N := C ⊓ Subgroup.normalizer (Qd : Set P45Q)
  have h64 : 64 ∣ Nat.card N := by
    rw [← card_TP]
    exact Subgroup.card_dvd_of_le (le_inf TP_le_C TP_le_normalizer)
  have h9 : 9 ∣ Nat.card N := nine_dvd_card_of_le ⟨s1Q_mem_C, s1Q_mem_normalizer⟩
    ⟨s2Q_mem_C, s2Q_mem_normalizer⟩
  have h576 : 576 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h9
  have hle : Nat.card N ≤ 576 := by
    rw [← qp45_card_centralizer_t]
    exact Subgroup.card_le_of_le inf_le_left
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hN : N = C := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [qp45_card_centralizer_t]
    exact Nat.le_of_dvd hpos h576)
  intro x hx
  rw [← hN] at hx
  exact hx.2

private theorem orderOf_s1s2invQ : orderOf (s1Q * s2Q⁻¹) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    exact s1s2inv_cube
  · intro h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h1
    exact s1s2inv_ne_one h1

theorem qp45_pCore_centralizer_t :
    inSubgroup (pCore 2) (Subgroup.centralizer ({tQ} : Set P45Q)) =
      Subgroup.closure {a1Q, b1Q, a2Q, b2Q} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({tQ} : Set P45Q) with hC
  have hQdC : Qd ≤ C := Qd_le_C
  have hQdn : ((Qd).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQdC).mpr C_le_normalizer_Qd
  have hcardQd : Nat.card ((Qd).subgroupOf C) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQdC).toEquiv, card_Qd]
  have hQd2 : IsPGroup 2 ((Qd).subgroupOf C) := IsPGroup.of_card (n := 5) hcardQd
  have hle1 : (Qd).subgroupOf C ≤ pCore 2 ↥C := le_sSup ⟨hQdn, hQd2⟩
  have hR : pCore 2 ↥C ≤ (Qd).subgroupOf C := by
    by_contra hnot
    have hRn : (pCore 2 ↥C).Normal := CFSG.pCore_normal
    have hR2 : IsPGroup 2 (pCore 2 ↥C) := CFSG.pCore_isPGroup
    have hX2 : IsPGroup 2 ↥(pCore 2 ↥C ⊔ (Qd).subgroupOf C) :=
      IsPGroup.to_sup_of_normal_right hR2 hQd2
    have hXn : (pCore 2 ↥C ⊔ (Qd).subgroupOf C).Normal := Subgroup.sup_normal _ _
    have hlt : (Qd).subgroupOf C < pCore 2 ↥C ⊔ (Qd).subgroupOf C :=
      lt_of_le_of_ne le_sup_right (fun h => hnot (h ▸ le_sup_left))
    obtain ⟨n, hn⟩ := hX2.exists_card_eq
    have hdvd : 2 ^ n ∣ 576 := by
      rw [← hn, ← qp45_card_centralizer_t]
      exact Subgroup.card_subgroup_dvd_card _
    have hgt : 32 < 2 ^ n := by
      rw [← hn, ← hcardQd]
      exact Subgroup.card_lt_of_lt hlt
    have hn6 : n = 6 := by
      have hle : n ≤ 6 := by
        by_contra h7
        have h128 : 2 ^ 7 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
        have := Nat.dvd_trans h128 hdvd
        norm_num at this
      have hge : 6 ≤ n := by
        by_contra h5
        have : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    have hXcard : Nat.card ↥(pCore 2 ↥C ⊔ (Qd).subgroupOf C) =
        2 ^ (Nat.card ↥C).factorization 2 := by
      rw [hn, hn6, qp45_card_centralizer_t, factorization_576]
    have hTcard : Nat.card ↥((sylowTwoQA45.comap ιQ).subgroupOf C) =
        2 ^ (Nat.card ↥C).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe TP_le_C).toEquiv, card_TP,
        qp45_card_centralizer_t, factorization_576]
      norm_num
    let SX : Sylow 2 ↥C := Sylow.ofCard _ hXcard
    let ST : Sylow 2 ↥C := Sylow.ofCard _ hTcard
    have hSX : (SX : Subgroup ↥C).Normal := hXn
    have huniq : Unique (Sylow 2 ↥C) := Sylow.unique_of_normal SX hSX
    have hST : ST = SX := Subsingleton.elim _ _
    have hTn : ((sylowTwoQA45.comap ιQ).subgroupOf C).Normal := by
      have h1 : ((ST : Subgroup ↥C)) = (sylowTwoQA45.comap ιQ).subgroupOf C := rfl
      rw [← h1, hST]
      exact hSX
    have huC : uQ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext t_commute_u.symm)
    let uC : ↥C := ⟨uQ, huC⟩
    let s1C : ↥C := ⟨s1Q, s1Q_mem_C⟩
    have huT : uC ∈ (sylowTwoQA45.comap ιQ).subgroupOf C := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      show uA ∈ sylowTwoQA45
      exact Subgroup.subset_closure (by simp)
    have hcomm : s1C * uC * s1C⁻¹ * uC⁻¹ ∈ (sylowTwoQA45.comap ιQ).subgroupOf C :=
      Subgroup.mul_mem _ (hTn.conj_mem _ huT _) (Subgroup.inv_mem _ huT)
    rw [Subgroup.mem_subgroupOf] at hcomm
    have heq : ((s1C * uC * s1C⁻¹ * uC⁻¹ : ↥C) : P45Q) = s1Q * s2Q⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact s1_u_comm
    rw [heq] at hcomm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp isPGroup_TP) ⟨s1Q * s2Q⁻¹, hcomm⟩
    rw [Subgroup.orderOf_mk, orderOf_s1s2invQ] at hk
    rcases k with _ | k
    · norm_num at hk
    · rw [pow_succ] at hk
      omega
  apply le_antisymm
  · rw [← Subgroup.map_subgroupOf_eq_of_le hQdC]
    exact Subgroup.map_mono hR
  · rw [← Subgroup.map_subgroupOf_eq_of_le hQdC]
    exact Subgroup.map_mono hle1

private theorem f1_eq_f2 {h h' : QuaternionGroup 2} (heq : f1 h = f2 h') :
    (h = 1 ∧ h' = 1) ∨ (h = a 2 ∧ h' = a 2) := by
  have hc : ∀ k : QuaternionGroup 2, h * k = k * h := by
    intro k
    apply f1_injective
    rw [map_mul, map_mul, heq, (commute_f1_f2 k h').eq.symm]
  have hc' : ∀ k : QuaternionGroup 2, h' * k = k * h' := by
    intro k
    apply f2_injective
    rw [map_mul, map_mul, ← heq, (commute_f1_f2 h k).eq]
  rcases q8_center hc with rfl | rfl <;> rcases q8_center hc' with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    rw [map_one, f2_a2] at heq
    exact tQ_ne_one heq.symm
  · exfalso
    rw [map_one, f1_a2] at heq
    exact tQ_ne_one heq
  · exact Or.inr ⟨rfl, rfl⟩

private theorem conj_s1_f1 (h : QuaternionGroup 2) : s1Q * f1 h * s1Q⁻¹ = f1 (q8Theta h) := by
  have hext : (MulAut.conj s1Q).toMonoidHom.comp f1 = f1.comp q8Theta := by
    apply q8_hom_ext
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q8Theta_a_one, f1_a1, f1_xa0,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s1_alpha1
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q8Theta_xa_zero, f1_xa0, f1_xa1,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s1_beta1'
  have h' := DFunLike.congr_fun hext h
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at h'
  exact h'

private theorem conj_s2_f2 (h : QuaternionGroup 2) : s2Q * f2 h * s2Q⁻¹ = f2 (q8Theta h) := by
  have hext : (MulAut.conj s2Q).toMonoidHom.comp f2 = f2.comp q8Theta := by
    apply q8_hom_ext
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q8Theta_a_one, f2_a1, f2_xa0,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s2_alpha2
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q8Theta_xa_zero, f2_xa0, f2_xa1,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s2_beta2'
  have h' := DFunLike.congr_fun hext h
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at h'
  exact h'

private theorem conj_s1_f2 (h : QuaternionGroup 2) : s1Q * f2 h * s1Q⁻¹ = f2 h := by
  have hext : (MulAut.conj s1Q).toMonoidHom.comp f2 = f2 := by
    apply q8_hom_ext
    · rw [MonoidHom.comp_apply, f2_a1, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s1_alpha2
    · rw [MonoidHom.comp_apply, f2_xa0, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s1_beta2
  have h' := DFunLike.congr_fun hext h
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
  exact h'

private theorem conj_s2_f1 (h : QuaternionGroup 2) : s2Q * f1 h * s2Q⁻¹ = f1 h := by
  have hext : (MulAut.conj s2Q).toMonoidHom.comp f1 = f1 := by
    apply q8_hom_ext
    · rw [MonoidHom.comp_apply, f1_a1, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s2_alpha1
    · rw [MonoidHom.comp_apply, f1_xa0, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subtype.ext s2_beta1
  have h' := DFunLike.congr_fun hext h
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h'
  exact h'

private theorem exists_conj_f1 {h : QuaternionGroup 2} (hh : h * h = a 2) :
    ∃ g : P45Q, g * f1 h * g⁻¹ = a1Q ∧ ∀ k, g * f2 k * g⁻¹ = f2 k := by
  have hfix : ∀ (q : QuaternionGroup 2) (k : QuaternionGroup 2), f1 q * f2 k * (f1 q)⁻¹ = f2 k :=
    fun q k => by rw [(commute_f1_f2 q k).eq, mul_inv_cancel_right]
  obtain ⟨q, hq | hq | hq⟩ := q8_exists_conj_theta hh
  · refine ⟨f1 q, ?_, hfix q⟩
    rw [← map_inv, ← map_mul, ← map_mul, hq, f1_a1]
  · refine ⟨f1 q * s1Q, ?_, fun k => ?_⟩
    · calc f1 q * s1Q * f1 h * (f1 q * s1Q)⁻¹ = f1 q * (s1Q * f1 h * s1Q⁻¹) * (f1 q)⁻¹ := by
            group
        _ = a1Q := by rw [conj_s1_f1, ← map_inv, ← map_mul, ← map_mul, hq, f1_a1]
    · calc f1 q * s1Q * f2 k * (f1 q * s1Q)⁻¹ = f1 q * (s1Q * f2 k * s1Q⁻¹) * (f1 q)⁻¹ := by
            group
        _ = f2 k := by rw [conj_s1_f2, hfix]
  · refine ⟨f1 q * s1Q * s1Q, ?_, fun k => ?_⟩
    · calc f1 q * s1Q * s1Q * f1 h * (f1 q * s1Q * s1Q)⁻¹ =
            f1 q * (s1Q * (s1Q * f1 h * s1Q⁻¹) * s1Q⁻¹) * (f1 q)⁻¹ := by group
        _ = a1Q := by
          rw [conj_s1_f1, conj_s1_f1, ← map_inv, ← map_mul, ← map_mul, hq, f1_a1]
    · calc f1 q * s1Q * s1Q * f2 k * (f1 q * s1Q * s1Q)⁻¹ =
            f1 q * (s1Q * (s1Q * f2 k * s1Q⁻¹) * s1Q⁻¹) * (f1 q)⁻¹ := by group
        _ = f2 k := by rw [conj_s1_f2, conj_s1_f2, hfix]

private theorem exists_conj_f2 {h : QuaternionGroup 2} (hh : h * h = a 2) :
    ∃ g : P45Q, g * f2 h * g⁻¹ = a2Q ∧ ∀ k, g * f1 k * g⁻¹ = f1 k := by
  have hfix : ∀ (q : QuaternionGroup 2) (k : QuaternionGroup 2), f2 q * f1 k * (f2 q)⁻¹ = f1 k :=
    fun q k => by rw [← (commute_f1_f2 k q).eq, mul_inv_cancel_right]
  obtain ⟨q, hq | hq | hq⟩ := q8_exists_conj_theta hh
  · refine ⟨f2 q, ?_, hfix q⟩
    rw [← map_inv, ← map_mul, ← map_mul, hq, f2_a1]
  · refine ⟨f2 q * s2Q, ?_, fun k => ?_⟩
    · calc f2 q * s2Q * f2 h * (f2 q * s2Q)⁻¹ = f2 q * (s2Q * f2 h * s2Q⁻¹) * (f2 q)⁻¹ := by
            group
        _ = a2Q := by rw [conj_s2_f2, ← map_inv, ← map_mul, ← map_mul, hq, f2_a1]
    · calc f2 q * s2Q * f1 k * (f2 q * s2Q)⁻¹ = f2 q * (s2Q * f1 k * s2Q⁻¹) * (f2 q)⁻¹ := by
            group
        _ = f1 k := by rw [conj_s2_f1, hfix]
  · refine ⟨f2 q * s2Q * s2Q, ?_, fun k => ?_⟩
    · calc f2 q * s2Q * s2Q * f2 h * (f2 q * s2Q * s2Q)⁻¹ =
            f2 q * (s2Q * (s2Q * f2 h * s2Q⁻¹) * s2Q⁻¹) * (f2 q)⁻¹ := by group
        _ = a2Q := by
          rw [conj_s2_f2, conj_s2_f2, ← map_inv, ← map_mul, ← map_mul, hq, f2_a1]
    · calc f2 q * s2Q * s2Q * f1 k * (f2 q * s2Q * s2Q)⁻¹ =
            f2 q * (s2Q * (s2Q * f1 k * s2Q⁻¹) * s2Q⁻¹) * (f2 q)⁻¹ := by group
        _ = f1 k := by rw [conj_s2_f1, conj_s2_f1, hfix]

private theorem conj_ut_a1a2Q : b1Q * bQ * a1Q * (uQ * tQ) * (b1Q * bQ * a1Q)⁻¹ = a1Q * a2Q :=
  ιQ_injective (by simp only [map_mul, map_inv]; exact conj_ut_alpha12_QA45)

theorem qp45_isConj_ut_of_mem_pCore_centralizer_t :
    ∀ j ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({tQ} : Set P45Q)), orderOf j = 2 →
      j ≠ tQ → IsConj j (uQ * tQ) := by
  intro j hj hj2 hjt
  rw [qp45_pCore_centralizer_t, ← range_fPhi] at hj
  obtain ⟨⟨h1, h2⟩, rfl⟩ := hj
  rw [fPhi_apply] at hj2 hjt ⊢
  have hjj : f1 h1 * f2 h2 * (f1 h1 * f2 h2) = 1 := by
    have h := pow_orderOf_eq_one (f1 h1 * f2 h2)
    rw [hj2, sq] at h
    exact h
  have hsq : f1 (h1 * h1) = f2 ((h2 * h2)⁻¹) := by
    rw [map_mul, map_inv, map_mul, eq_inv_iff_mul_eq_one]
    have hc := (commute_f1_f2 h1 h2).eq
    calc f1 h1 * f1 h1 * (f2 h2 * f2 h2) = f1 h1 * (f1 h1 * f2 h2) * f2 h2 := by group
      _ = f1 h1 * (f2 h2 * f1 h1) * f2 h2 := by rw [hc]
      _ = f1 h1 * f2 h2 * (f1 h1 * f2 h2) := by group
      _ = 1 := hjj
  have hj1 : f1 h1 * f2 h2 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hj2
    omega
  rcases f1_eq_f2 hsq with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · exfalso
    rw [inv_eq_one] at hh2
    rcases q8_sq_eq_one hh1 with rfl | rfl <;> rcases q8_sq_eq_one hh2 with rfl | rfl
    · exact hj1 (by rw [map_one, map_one, mul_one])
    · exact hjt (by rw [map_one, one_mul, f2_a2])
    · exact hjt (by rw [map_one, mul_one, f1_a2])
    · exact hj1 (by rw [f1_a2, f2_a2]; exact Subtype.ext t_sq)
  · have hh2' : h2 * h2 = a 2 := by
      rw [← inv_inv (h2 * h2), hh2]
      decide
    obtain ⟨g1, hg1, hg1'⟩ := exists_conj_f1 hh1
    obtain ⟨g2, hg2, hg2'⟩ := exists_conj_f2 hh2'
    have hconj : IsConj (f1 h1 * f2 h2) (a1Q * a2Q) := by
      refine isConj_iff.mpr ⟨g2 * g1, ?_⟩
      calc g2 * g1 * (f1 h1 * f2 h2) * (g2 * g1)⁻¹ =
            g2 * ((g1 * f1 h1 * g1⁻¹) * (g1 * f2 h2 * g1⁻¹)) * g2⁻¹ := by group
        _ = g2 * (f1 (a 1) * f2 h2) * g2⁻¹ := by rw [hg1, hg1', f1_a1]
        _ = (g2 * f1 (a 1) * g2⁻¹) * (g2 * f2 h2 * g2⁻¹) := by group
        _ = a1Q * a2Q := by rw [hg2', hg2, f1_a1]
    have hut : IsConj (uQ * tQ) (a1Q * a2Q) := isConj_iff.mpr ⟨_, conj_ut_a1a2Q⟩
    exact hconj.trans hut.symm

theorem qp45_not_isConj_of_mem_pCore_centralizer
    {x y : P45Q} (hx : orderOf x = 2) (hxc : Nat.card (Subgroup.centralizer ({x} : Set P45Q)) = 576)
    (hy : y ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({x} : Set P45Q)))
    (hy2 : orderOf y = 2) (hyx : y ≠ x) : ¬ IsConj x y := by
  intro hxy
  have hxt : IsConj x tQ := by
    rcases qp45_involution_classes x hx with h | h
    · exact h
    · exfalso
      have h1 := CFSG.GroupTheory.card_centralizer_eq_of_isConj h
      rw [hxc, qp45_card_centralizer_ut] at h1
      omega
  obtain ⟨c, hc⟩ := isConj_iff.mp hxt
  have hy' : MulAut.conj c y ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({tQ} : Set P45Q)) := by
    rw [← hc, show c * x * c⁻¹ = MulAut.conj c x from rfl,
      ← map_inSubgroup_pCore_centralizer (MulAut.conj c) x]
    exact Subgroup.mem_map_of_mem _ hy
  have hy'2 : orderOf (MulAut.conj c y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy2
  have hy't : MulAut.conj c y ≠ tQ := by
    rw [← hc]
    intro h
    exact hyx ((MulAut.conj c).injective h)
  have h1 := qp45_isConj_ut_of_mem_pCore_centralizer_t _ hy' hy'2 hy't
  apply qp45_not_isConj_t_ut
  exact hxt.symm.trans (hxy.trans ((isConj_iff.mpr ⟨c, rfl⟩).trans h1))

theorem not_isConj_of_mem_pCore_centralizer_of_lieModel
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 2 3 1) {x y : X}
    (hx : orderOf x = 2) (hxc : Nat.card (Subgroup.centralizer ({x} : Set X)) = 576)
    (hy : y ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({x} : Set X)))
    (hy2 : orderOf y = 2) (hyx : y ≠ x) : ¬ IsConj x y := by
  obtain ⟨e⟩ := equiv_of_lieModel hX
  intro hxy
  refine qp45_not_isConj_of_mem_pCore_centralizer (x := e x) (y := e y) ?_ ?_ ?_ ?_ ?_
    (MonoidHom.map_isConj e.toMonoidHom hxy)
  · rw [MulEquiv.orderOf_eq]
    exact hx
  · rw [card_centralizer_map]
    exact hxc
  · rw [← map_inSubgroup_pCore_centralizer e x]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [MulEquiv.orderOf_eq]
    exact hy2
  · intro h
    exact hyx (e.injective h)

end CFSG.RankThree.GF2n.Parrott
