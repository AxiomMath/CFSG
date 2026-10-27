module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.NoncommCoprod

import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_center_left {g h c : G} (hc : c ∈ center G) :
    ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have hch := mem_center_iff.1 hc h
  calc ⁅g * c, h⁆ = g * (c * h) * c⁻¹ * g⁻¹ * h⁻¹ := by rw [commutatorElement_def]; group
    _ = g * (h * c) * c⁻¹ * g⁻¹ * h⁻¹ := by rw [hch]
    _ = ⁅g, h⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_mul_center_right {g h c : G} (hc : c ∈ center G) :
    ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have hcg := mem_center_iff.1 hc g⁻¹
  calc ⁅g, h * c⁆ = g * h * (c * g⁻¹) * c⁻¹ * h⁻¹ := by rw [commutatorElement_def]; group
    _ = g * h * (g⁻¹ * c) * c⁻¹ * h⁻¹ := by rw [hcg]
    _ = ⁅g, h⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_mul_right_of_commute {g h k : G} (hk : Commute g k) :
    ⁅g, h * k⁆ = ⁅g, h⁆ := by
  calc ⁅g, h * k⁆ = g * h * (k * g⁻¹ * k⁻¹) * h⁻¹ := by rw [commutatorElement_def]; group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [← hk.inv_left.eq, mul_inv_cancel_right]
    _ = ⁅g, h⁆ := (commutatorElement_def g h).symm

theorem commutatorElement_pow_pow_of_mem_center {g h : G} (hc : ⁅g, h⁆ ∈ center G) (m n : ℕ) :
    ⁅g ^ m, h ^ n⁆ = ⁅g, h⁆ ^ (m * n) := by
  have hn : ⁅g, h ^ n⁆ = ⁅g, h⁆ ^ n :=
    (Commute.commutatorElement_pow_right (show Commute h ⁅g, h⁆ from mem_center_iff.1 hc h)
      n).symm
  have hc' : ⁅g, h ^ n⁆ ∈ center G := hn ▸ pow_mem hc n
  rw [← Commute.commutatorElement_pow_left
      (show Commute g ⁅g, h ^ n⁆ from mem_center_iff.1 hc' g) m, hn, ← pow_mul, Nat.mul_comm]

theorem commutatorElement_mem_center_of_eq {Q : Type*} [Group Q]
    (hZQ : center Q = commutator Q) (x y : Q) : ⁅x, y⁆ ∈ center Q :=
  hZQ ▸ commutator_mem_commutator (mem_top x) (mem_top y)

theorem mk_eq_pow_iff_mem_center {Q : Type*} [Group Q] (x y : Q) (r : ℕ) :
    (QuotientGroup.mk x : Q ⧸ center Q) = (QuotientGroup.mk y) ^ r ↔
      (y ^ r)⁻¹ * x ∈ center Q := by
  rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]

end Commutators

variable {U Q : Type*} [Group U] [Group Q] {p : ℕ} [hp : Fact p.Prime]

section Scalars

theorem neg_one_ne_one_zmod (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
    rw [this, h, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)

theorem natCast_pred_eq_neg_one : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp.out.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem natCast_pred_ne_one (hp2 : p ≠ 2) : ((p - 1 : ℕ) : ZMod p) ≠ 1 := by
  rw [natCast_pred_eq_neg_one]
  exact neg_one_ne_one_zmod hp2

theorem natCast_pred_pow_three_ne_one (hp2 : p ≠ 2) : ((p - 1 : ℕ) : ZMod p) ^ 3 ≠ 1 := by
  rw [natCast_pred_eq_neg_one, show (-1 : ZMod p) ^ 3 = -1 by ring]
  exact neg_one_ne_one_zmod hp2

theorem det_one_pred_ne_zero (hp2 : p ≠ 2) :
    (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) *
        (((1 : ℕ) : ZMod p) * ((p - 1 : ℕ) : ZMod p) - 1) -
      ((1 : ℕ) : ZMod p) ^ 2 * ((0 : ℕ) : ZMod p) * ((0 : ℕ) : ZMod p) ≠ 0 := by
  rw [natCast_pred_eq_neg_one]
  have h4 : (((1 : ℕ) : ZMod p) * (-1) - 1) * (((1 : ℕ) : ZMod p) * (-1) - 1) -
      ((1 : ℕ) : ZMod p) ^ 2 * ((0 : ℕ) : ZMod p) * ((0 : ℕ) : ZMod p) =
        ((2 ^ 2 : ℕ) : ZMod p) := by
    push_cast; ring
  rw [h4]
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))

theorem pow_pred_eq_inv {G : Type*} [Group G] {x : G} (hx : x ^ p = 1) : x ^ (p - 1) = x⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, hx])

end Scalars

theorem comap_center_le_center_of_scalar (π : U →* Q) (hπ : Function.Surjective π)
    (hC : π.ker ≤ center U) (hQexp : ∀ q : Q, q ^ p = 1) (hZQ : center Q = commutator Q)
    (hZcard : Nat.card (center Q) = p) (a : MulAut U) (hfix : ∀ c ∈ π.ker, a c = c) (r : ℕ)
    (hr : ∀ u : U, (π u ^ r)⁻¹ * π (a u) ∈ center Q) (hr3 : (r : ZMod p) ^ 3 ≠ 1) :
    (center Q).comap π ≤ center U := by
  set W := (center Q).comap π with hW
  have hQc := commutatorElement_mem_center_of_eq hZQ
  have hstep : ∀ x y : U, π (a ⁅x, y⁆) = π ⁅x, y⁆ ^ (r * r) := by
    intro x y
    have hx := hr x
    have hy := hr y
    rw [map_commutatorElement, map_commutatorElement, map_commutatorElement,
      ← mul_inv_cancel_left (π x ^ r) (π (a x)), ← mul_inv_cancel_left (π y ^ r) (π (a y)),
      commutatorElement_mul_center_left hx, commutatorElement_mul_center_right hy,
      commutatorElement_pow_pow_of_mem_center (hQc _ _)]
  have hcomm : ∀ g ∈ commutator U, π g ∈ center Q ∧ π (a g) = π g ^ (r * r) := by
    intro g hg
    simp only [_root_.commutator_def, commutator_def] at hg
    induction hg using closure_induction with
    | mem g hg =>
      obtain ⟨x, -, y, -, rfl⟩ := hg
      exact ⟨by rw [map_commutatorElement]; exact hQc _ _, hstep x y⟩
    | one => exact ⟨by rw [map_one]; exact one_mem _, by rw [map_one, map_one, one_pow]⟩
    | mul g h _ _ hg hh =>
      refine ⟨by rw [map_mul]; exact mul_mem hg.1 hh.1, ?_⟩
      rw [map_mul, map_mul, map_mul, hg.2, hh.2,
        Commute.mul_pow (show Commute (π g) (π h) from (mem_center_iff.1 hg.1 (π h)).symm)]
    | inv g _ hg =>
      exact ⟨by rw [map_inv]; exact inv_mem hg.1, by rw [map_inv, map_inv, map_inv, hg.2, inv_pow]⟩
  have hmapW : (commutator U).map π = commutator Q := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective π hπ]
  have hW2 : ∀ w ∈ W, π (a w) = π w ^ (r * r) := by
    intro w hw
    have hw' : π w ∈ (commutator U).map π := by rw [hmapW, ← hZQ]; exact hw
    obtain ⟨g, hg, hgw⟩ := hw'
    have hc : g⁻¹ * w ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hgw, inv_mul_cancel]
    conv_lhs => rw [← mul_inv_cancel_left g w]
    rw [map_mul, map_mul, hfix _ hc, (MonoidHom.mem_ker).1 hc, mul_one, (hcomm g hg).2, hgw]
  have hWab : ∀ w ∈ W, ∀ w' ∈ W, Commute w w' := by
    have : IsCyclic (center Q) := isCyclic_of_prime_card hZcard
    let f : W →* center Q := (π.domRestrict W).codRestrict (center Q) fun w => w.2
    have hker : f.ker ≤ center W := by
      intro w hw
      have hw' : (w : U) ∈ π.ker := congrArg Subtype.val hw
      exact mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 (hC hw') g)
    have hWc := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker
    intro w hw w' hw'
    exact congrArg Subtype.val (hWc.is_comm.comm ⟨w, hw⟩ ⟨w', hw'⟩)
  intro w hw
  rw [mem_center_iff]
  intro u
  set k := ⁅w, u⁆ with hk
  have hkker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker, hk, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 hw (π u)).symm
  have hkc : k ∈ center U := hC hkker
  have hc₁ : (w ^ (r * r))⁻¹ * a w ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hW2 w hw, inv_mul_cancel]
  have hw₂ : (u ^ r)⁻¹ * a u ∈ W := by
    rw [hW, mem_comap, map_mul, map_inv, map_pow]
    exact hr u
  have hwpow : w ^ (r * r) ∈ W := pow_mem hw _
  have hkr : k = k ^ (r * r * r) := by
    calc k = a k := (hfix k hkker).symm
      _ = ⁅a w, a u⁆ := by rw [hk, map_commutatorElement]
      _ = ⁅w ^ (r * r) * ((w ^ (r * r))⁻¹ * a w), u ^ r * ((u ^ r)⁻¹ * a u)⁆ := by
          rw [mul_inv_cancel_left, mul_inv_cancel_left]
      _ = ⁅w ^ (r * r), u ^ r⁆ := by
          rw [commutatorElement_mul_center_left (hC hc₁),
            commutatorElement_mul_right_of_commute (hWab _ hwpow _ hw₂)]
      _ = k ^ (r * r * r) := by rw [commutatorElement_pow_pow_of_mem_center hkc, hk]
  have hkp : k ^ p = 1 := by
    have hwp : w ^ p ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hQexp]
    rw [hk, Commute.commutatorElement_pow_left
        (show Commute w ⁅w, u⁆ from mem_center_iff.1 hkc w) p,
      commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 (hC hwp) u).symm
  have hk1 : k = 1 := by
    by_contra hne
    have hord : orderOf k = p := orderOf_eq_prime hkp hne
    have h := hkr
    nth_rewrite 1 [← pow_one k] at h
    rw [pow_eq_pow_iff_modEq, hord] at h
    apply hr3
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h.symm
    push_cast at this
    rw [← this]
    ring
  rw [hk, commutatorElement_eq_one_iff_mul_comm] at hk1
  exact hk1.symm

theorem map_eq_top_of_scalar (π : U →* Q) (hπ : Function.Surjective π)
    (hQexp : ∀ q : Q, q ^ p = 1) (hZQ : center Q = commutator Q) {S : Subgroup U}
    (a : MulAut U) (haS : ∀ u, u⁻¹ * a u ∈ S) (r : ℕ)
    (hr : ∀ u : U, (π u ^ r)⁻¹ * π (a u) ∈ center Q) (hr1 : (r : ZMod p) ≠ 1) :
    S.map π = ⊤ := by
  set X := S.map π with hX
  have hQc := commutatorElement_mem_center_of_eq hZQ
  have hdec : ∀ q : Q, ∃ x ∈ X, x⁻¹ * q ∈ center Q := by
    intro q
    obtain ⟨u, rfl⟩ := hπ q
    have hunit : ((r : ZMod p) - 1) ≠ 0 := sub_ne_zero.2 hr1
    set k := (((r : ZMod p) - 1)⁻¹).val with hkdef
    have hk : ((k : ℤ) * ((r : ℤ) - 1) : ZMod p) = 1 := by
      push_cast
      rw [hkdef, ZMod.natCast_zmod_val, inv_mul_cancel₀ hunit]
    set w := u ^ k with hw
    refine ⟨π (w⁻¹ * a w), mem_map_of_mem π (haS w), ?_⟩
    have hζ := hr w
    set ζ := (π w ^ r)⁻¹ * π (a w) with hζdef
    have haw : π (a w) = π w ^ r * ζ := by rw [hζdef, mul_inv_cancel_left]
    have hpow : π w ^ ((r : ℤ) - 1) = π u := by
      rw [hw, map_pow, ← zpow_natCast, ← zpow_mul]
      have hord : orderOf (π u) ∣ p := orderOf_dvd_of_pow_eq_one (hQexp _)
      rw [zpow_eq_zpow_iff_modEq.2 ?_, zpow_one]
      have hmod : ((k : ℤ) * ((r : ℤ) - 1)) ≡ 1 [ZMOD p] := by
        rw [← ZMod.intCast_eq_intCast_iff]
        push_cast at hk ⊢
        exact hk
      exact hmod.of_dvd (Int.natCast_dvd_natCast.2 hord)
    have hπs : π (w⁻¹ * a w) = π u * ζ := by
      rw [map_mul, map_inv, haw, ← mul_assoc, ← hpow, zpow_sub_one, ← zpow_natCast,
        ← zpow_neg_one, ← zpow_add, ← zpow_add]
      congr 2
    rw [hπs, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hζ
  have hcomm : commutator Q ≤ X := by
    rw [_root_.commutator_def, commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨x₁, hx₁, h₁⟩ := hdec g₁
    obtain ⟨x₂, hx₂, h₂⟩ := hdec g₂
    rw [← mul_inv_cancel_left x₁ g₁, ← mul_inv_cancel_left x₂ g₂,
      commutatorElement_mul_center_left h₁, commutatorElement_mul_center_right h₂]
    exact commutatorElement_def x₁ x₂ ▸
      X.mul_mem (X.mul_mem (X.mul_mem hx₁ hx₂) (X.inv_mem hx₁)) (X.inv_mem hx₂)
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨x, hx, hxq⟩ := hdec q
  rw [← mul_inv_cancel_left x q]
  exact X.mul_mem hx (hcomm (hZQ ▸ hxq))

@[expose] def autCommutator (A : Subgroup (MulAut U)) : Subgroup U :=
  closure {g | ∃ u, ∃ a ∈ A, g = u⁻¹ * a u}

theorem inv_mul_apply_mem_autCommutator {A : Subgroup (MulAut U)} (u : U) {a : MulAut U}
    (ha : a ∈ A) : u⁻¹ * a u ∈ autCommutator A :=
  subset_closure ⟨u, a, ha, rfl⟩

omit hp in
theorem invariant_complement_of_map_eq_top [Finite U] (π : U →* Q) (hC : π.ker ≤ center U)
    (hCp : IsPGroup p π.ker) (A : Subgroup (MulAut U)) [Finite A] (hA : (Nat.card A).Coprime p)
    (hfix : ∀ a ∈ A, ∀ c ∈ π.ker, a c = c) (hCU : π.ker ⊓ commutator U = ⊥)
    (hD : (autCommutator A).map π = ⊤) :
    (∀ a ∈ A, ∀ d ∈ autCommutator A, a d ∈ autCommutator A) ∧ π.ker ⊔ autCommutator A = ⊤ ∧
      π.ker ⊓ autCommutator A = ⊥ ∧ commutator U ≤ autCommutator A ∧
      (autCommutator A).Normal ∧ Function.Bijective (π.domRestrict (autCommutator A)) ∧
      ∀ D' : Subgroup U, (∀ a ∈ A, ∀ d ∈ D', a d ∈ D') → π.ker ⊔ D' = ⊤ → π.ker ⊓ D' = ⊥ →
        D' = autCommutator A := by
  classical
  set D := autCommutator A with hDdef
  have hlift : ∀ x : U, ∃ d ∈ D, d⁻¹ * x ∈ π.ker := by
    intro x
    obtain ⟨d, hd, hdx⟩ : π x ∈ D.map π := by rw [hD]; exact mem_top _
    exact ⟨d, hd, by rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]⟩
  have hsurj : Function.Surjective π := fun q => by
    obtain ⟨d, -, hdq⟩ : q ∈ D.map π := by rw [hD]; exact mem_top _
    exact ⟨d, hdq⟩
  have hinv : ∀ a ∈ A, ∀ d ∈ D, a d ∈ D := by
    intro a ha d hd
    induction hd using closure_induction with
    | mem g hg =>
      obtain ⟨u, b, hb, rfl⟩ := hg
      have hconj : a * b * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)
      have h := inv_mul_apply_mem_autCommutator (a u) hconj
      rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
        ← map_inv, ← map_mul] at h
    | one => rw [map_one]; exact D.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact D.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact D.inv_mem hx
  have hsup : π.ker ⊔ D = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨d, hd, hdx⟩ := hlift x
    have h := mul_mem_sup hd hdx
    rwa [mul_inv_cancel_left, sup_comm] at h
  have hcommD : commutator U ≤ D := by
    rw [_root_.commutator_def, commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨d₁, hd₁, h₁⟩ := hlift g₁
    obtain ⟨d₂, hd₂, h₂⟩ := hlift g₂
    rw [← mul_inv_cancel_left d₁ g₁, ← mul_inv_cancel_left d₂ g₂,
      commutatorElement_mul_center_left (hC h₁), commutatorElement_mul_center_right (hC h₂),
      commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)
  have hnormal : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have h : ⁅g, d⁆ ∈ D := hcommD (commutator_mem_commutator (mem_top g) (mem_top d))
    have h' := D.mul_mem h hd
    rwa [commutatorElement_def, inv_mul_cancel_right] at h'
  have : Fintype A := Fintype.ofFinite A
  let e : U →* Abelianization U :=
    { toFun := fun u => ∏ a : A, Abelianization.of ((a : MulAut U) u)
      map_one' := by simp
      map_mul' := fun u v => by simp only [map_mul, Finset.prod_mul_distrib] }
  have he : ∀ u, e u = ∏ a : A, Abelianization.of ((a : MulAut U) u) := fun u => rfl
  have heD : D ≤ e.ker := by
    rw [hDdef, autCommutator, closure_le]
    rintro _ ⟨u, b, hb, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, he, he]
    have hre := Equiv.prod_comp (Equiv.mulRight (⟨b, hb⟩ : A))
      (fun a : A => Abelianization.of ((a : MulAut U) u))
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, MulAut.mul_apply] at hre
    rw [hre, inv_mul_cancel]
  have hinf : π.ker ⊓ D = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC, hcD⟩ := mem_inf.1 hc
    have hec : e c = Abelianization.of (c ^ Fintype.card A) := by
      rw [he, map_pow, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_congr rfl fun a _ => by rw [hfix _ a.2 c hcC]
    have h1 : c ^ Fintype.card A ∈ commutator U := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker, ← hec]
      exact heD hcD
    obtain ⟨k, hk⟩ := hCp ⟨c, hcC⟩
    have hk' : c ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : (Fintype.card A).Coprime (orderOf c) := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk') (hA.pow_right k)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hcU : c ∈ commutator U := hm ▸ pow_mem h1 m
    rw [← hCU]
    exact mem_inf.2 ⟨hcC, hcU⟩
  have hinj : ∀ {H : Subgroup U}, π.ker ⊓ H = ⊥ → Function.Injective (π.domRestrict H) := by
    intro H hH
    rw [injective_iff_map_eq_one]
    intro h hh
    have hh' : (h : U) ∈ π.ker ⊓ H := mem_inf.2 ⟨hh, h.2⟩
    rw [hH] at hh'
    exact Subtype.ext ((mem_bot).1 hh')
  have hbij : Function.Bijective (π.domRestrict D) := by
    refine ⟨hinj hinf, fun q => ?_⟩
    obtain ⟨d, hd, hdq⟩ : q ∈ D.map π := by rw [hD]; exact mem_top _
    exact ⟨⟨d, hd⟩, hdq⟩
  refine ⟨hinv, hsup, hinf, hcommD, hnormal, hbij, ?_⟩
  intro D' hinv' hsup' hinf'
  have hDD' : D ≤ D' := by
    rw [hDdef, autCommutator, closure_le]
    rintro _ ⟨u, b, hb, rfl⟩
    have hu : u ∈ π.ker ⊔ D' := by rw [hsup']; exact mem_top u
    obtain ⟨c, hc, d', hd', rfl⟩ := mem_sup_of_normal_left.1 hu
    have h : (c * d')⁻¹ * b (c * d') = d'⁻¹ * b d' := by
      rw [map_mul, hfix b hb c hc, mul_inv_rev, mul_assoc, ← mul_assoc c⁻¹, inv_mul_cancel,
        one_mul]
    rw [SetLike.mem_coe, h]
    exact D'.mul_mem (D'.inv_mem hd') (hinv' b hb d' hd')
  have hbij' : Function.Bijective (π.domRestrict D') := by
    refine ⟨hinj hinf', fun q => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj q
    have hx : x ∈ π.ker ⊔ D' := by rw [hsup']; exact mem_top x
    obtain ⟨c, hc, d', hd', rfl⟩ := mem_sup_of_normal_left.1 hx
    refine ⟨⟨d', hd'⟩, ?_⟩
    rw [MonoidHom.domRestrict_apply, map_mul, (MonoidHom.mem_ker).1 hc, one_mul]
  have hcard : Nat.card D' ≤ Nat.card D := by
    rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_of_bijective _ hbij']
  exact (eq_of_le_of_card_ge hDD' hcard).symm

section Automorphisms

theorem zpowers_invariant_of_invariant {α : MulAut U} (hα : IsOfFinOrder α) {D : Subgroup U}
    (hD : ∀ d ∈ D, α d ∈ D) : ∀ a ∈ zpowers α, ∀ d ∈ D, a d ∈ D := by
  intro a ha
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hα.mem_powers_iff_mem_zpowers.2 ha)
  clear ha
  induction k with
  | zero => intro d hd; simpa using hd
  | succ k ih => intro d hd; rw [pow_succ', MulAut.mul_apply]; exact hD _ (ih d hd)

theorem zpowers_fix_of_fix {α : MulAut U} (hα : IsOfFinOrder α) {S : Set U}
    (hS : ∀ c ∈ S, α c = c) : ∀ a ∈ zpowers α, ∀ c ∈ S, a c = c := by
  intro a ha
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hα.mem_powers_iff_mem_zpowers.2 ha)
  clear ha
  induction k with
  | zero => intro c _; rfl
  | succ k ih => intro c hc; rw [pow_succ', MulAut.mul_apply, ih c hc, hS c hc]

theorem exists_mulEquiv_prod_of_central {C D : Subgroup U} (hC : C ≤ center U)
    (hsup : C ⊔ D = ⊤) (hinf : C ⊓ D = ⊥) :
    ∃ e : C × D ≃* U, ∀ c d, e (c, d) = (c : U) * d := by
  have : C.Normal := normal_of_le_center hC
  let f : C × D →* U := MonoidHom.noncommCoprod C.subtype D.subtype fun c d =>
    (mem_center_iff.1 (hC c.2) d).symm
  have hf : ∀ c d, f (c, d) = (c : U) * d := fun c d => rfl
  have hfbij : Function.Bijective f := by
    refine ⟨?_, fun x => ?_⟩
    · rw [injective_iff_map_eq_one]
      rintro ⟨c, d⟩ h
      rw [hf] at h
      have hdc : (d : U) = (c : U)⁻¹ := eq_inv_of_mul_eq_one_right h
      have hd1 : (d : U) = 1 := by
        have hmem : (d : U) ∈ C ⊓ D := mem_inf.2 ⟨hdc ▸ C.inv_mem c.2, d.2⟩
        rw [hinf] at hmem
        exact (mem_bot).1 hmem
      have hc1 : (c : U) = 1 := by rw [hd1, mul_one] at h; exact h
      exact Prod.ext (Subtype.ext hc1) (Subtype.ext hd1)
    · have hx : x ∈ C ⊔ D := by rw [hsup]; exact mem_top x
      obtain ⟨c, hc, d, hd, rfl⟩ := mem_sup_of_normal_left.1 hx
      exact ⟨(⟨c, hc⟩, ⟨d, hd⟩), rfl⟩
  exact ⟨MulEquiv.ofBijective f hfbij, hf⟩

end Automorphisms

end CFSG.RankThree.CentralExtension
