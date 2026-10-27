module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.RonanF95

lemma ndF95_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

lemma ndF95_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

lemma ndF95_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

lemma ndF95_symm {A : Type*} [CommGroup A] (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hβalt : ∀ x, β x x = 0) (u v : A) : β u v = β v u := by
  have e1 : β (u * v) (u * v) = β u u + β u v + (β v u + β v v) := by
    rw [hβl, hβr, hβr]
  have hz := hβalt (u * v)
  rw [e1, hβalt u, hβalt v, zero_add, add_zero] at hz
  exact ndF95_eq_of_add_eq_zero hz

lemma ndF95_zero_left {A : Type*} [CommGroup A] (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (z : A) : β 1 z = 0 := by
  have h := hβl 1 1 z
  rw [mul_one] at h
  exact h.trans (ndF95_add_self _)

lemma ndF95_zero_right {A : Type*} [CommGroup A] (β : A → A → ZMod 2)
    (hβr : ∀ x y z, β x (y * z) = β x y + β x z) (z : A) : β z 1 = 0 := by
  have h := hβr z 1 1
  rw [mul_one] at h
  exact h.trans (ndF95_add_self _)

lemma ndF95_iso {A : Type*} [CommGroup A] (q : A → ZMod 2) (β : A → A → ZMod 2)
    (hq : ∀ x y, q (x * y) = q x + q y + β x y) (S : Subgroup A) (hS : ∀ x ∈ S, q x = 0)
    (x y : A) (hx : x ∈ S) (hy : y ∈ S) : β x y = 0 := by
  have h := hq x y
  rw [hS x hx, hS y hy, hS (x * y) (S.mul_mem hx hy), zero_add, zero_add] at h
  exact h.symm

lemma ndF95_nbInj {A : Type*} [CommGroup A] (hexp : ∀ x : A, x * x = 1) (b : A ≃* A)
    (X Y : Subgroup A) (hXY : IsCompl X Y) (hYb : ∀ y, y ∈ Y ↔ b y = y) :
    ∀ x ∈ X, ∀ x' ∈ X, b x * x = b x' * x' → x = x' := by
  have hker : ∀ z ∈ X, b z * z = 1 → z = 1 := by
    intro z hz hbz
    have hbz' : b z = z :=
      (eq_inv_of_mul_eq_one_left hbz).trans (inv_eq_of_mul_eq_one_right (hexp z))
    have hzb : z ∈ X ⊓ Y := Subgroup.mem_inf.2 ⟨hz, (hYb z).2 hbz'⟩
    rw [hXY.inf_eq_bot] at hzb
    exact Subgroup.mem_bot.1 hzb
  intro x hx x' hx' h
  have hprod : b (x * x') * (x * x') = 1 := by
    have e : b (x * x') * (x * x') = (b x * x) * (b x' * x') := by
      rw [map_mul]; ac_rfl
    rw [e, ← h]
    exact hexp _
  have h1 : x * x' = 1 := hker (x * x') (X.mul_mem hx hx') hprod
  exact ((eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right (hexp x))).symm

lemma ndF95_nbSurj {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (b : A ≃* A) (X Y : Subgroup A) (hXY : IsCompl X Y) (hYb : ∀ y, y ∈ Y ↔ b y = y)
    (hbY : ∀ y, b y * y ∈ Y) (hcard : Nat.card X = Nat.card Y) :
    ∀ y ∈ Y, ∃ x ∈ X, b x * x = y := by
  have hf : Function.Injective (fun x : X => (⟨b x * x, hbY x⟩ : Y)) := by
    intro x x' h
    apply Subtype.ext
    exact ndF95_nbInj hexp b X Y hXY hYb x x.2 x' x'.2 (congrArg Subtype.val h)
  have hsurj := (hf.bijective_of_nat_card_le hcard.symm.le).2
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

lemma ndF95_cardLe {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (b : A ≃* A) (X Y : Subgroup A) (hXY : IsCompl X Y) (hYb : ∀ y, y ∈ Y ↔ b y = y)
    (hbY : ∀ y, b y * y ∈ Y) : Nat.card X ≤ Nat.card Y := by
  apply Nat.card_le_card_of_injective (fun x : X => (⟨b x * x, hbY x⟩ : Y))
  intro x x' h
  apply Subtype.ext
  exact ndF95_nbInj hexp b X Y hXY hYb x x.2 x' x'.2 (congrArg Subtype.val h)

lemma ndF95_twoNsmul {A : Type*} [CommGroup A] (hexp : ∀ x : A, x * x = 1) (X : Subgroup A)
    (v : Additive X) : (2 : ℕ) • v = 0 := by
  rw [two_nsmul]
  exact Subtype.ext (hexp ((Additive.toMul v : X) : A))

lemma ndF95_leftTrivial {K V W : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (B : V →ₗ[K] W →ₗ[K] K)
    (hfin : Module.finrank K V = Module.finrank K W)
    (hW : ∀ w : W, (∀ v : V, B v w = 0) → w = 0) (v : V) (hv : ∀ w : W, B v w = 0) :
    v = 0 := by
  by_contra hne
  have hinj : Function.Injective (LinearMap.flip B) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hW w
    intro v'
    exact LinearMap.congr_fun hw v'
  haveI : Finite (Module.Dual K V) := Module.finite_of_finite (R := K) (M := Module.Dual K V)
  have hcardD : Nat.card (Module.Dual K V) = Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Module.Dual K V),
      Module.natCard_eq_pow_finrank (K := K) (V := W), Subspace.dual_finrank_eq, hfin]
  have hsurj := (hinj.bijective_of_nat_card_le hcardD.le).2
  have hφex : ∃ φ : Module.Dual K V, φ v ≠ 0 := by
    by_contra h
    have h' : ∀ φ : Module.Dual K V, φ v = 0 := fun φ => by
      by_contra hφ
      exact h ⟨φ, hφ⟩
    exact hne ((Module.forall_dual_apply_eq_zero_iff K v).mp h')
  obtain ⟨φ, hφ⟩ := hφex
  obtain ⟨w, hw⟩ := hsurj φ
  apply hφ
  rw [← hw, LinearMap.flip_apply]
  exact hv w

lemma ndF95_radX {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (q : A → ZMod 2) (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hq : ∀ x y, q (x * y) = q x + q y + β x y) (hβalt : ∀ x, β x x = 0)
    (b : A ≃* A) (hqb : ∀ x, q (b x) = q x)
    (X Y : Subgroup A) (hYb : ∀ y, y ∈ Y ↔ b y = y) (hbY : ∀ y, b y * y ∈ Y)
    (hXY : IsCompl X Y) (hqX : ∀ x ∈ X, q x = 0) (hqY : ∀ y ∈ Y, q y = 0)
    (hX : Nat.card X = 4) (hY : Nat.card Y = 4) (hβ0 : ∃ x y, β x y ≠ 0)
    (x₁ : A) (hx₁ : x₁ ∈ X) (hrad : ∀ x'' ∈ X, β x₁ (b x'' * x'') = 0) : x₁ = 1 := by
  have hsymm := ndF95_symm β hβl hβr hβalt
  have hXiso : ∀ u ∈ X, ∀ v ∈ X, β u v = 0 := fun u hu v hv =>
    ndF95_iso q β hq X hqX u v hu hv
  have hYiso : ∀ u ∈ Y, ∀ v ∈ Y, β u v = 0 := fun u hu v hv =>
    ndF95_iso q β hq Y hqY u v hu hv
  have hsurj : ∀ y ∈ Y, ∃ x ∈ X, b x * x = y :=
    ndF95_nbSurj hexp b X Y hXY hYb hbY (hX.trans hY.symm)
  have hβ1 : ∀ z, β 1 z = 0 := ndF95_zero_left β hβl
  have hβ1r : ∀ z, β z 1 = 0 := ndF95_zero_right β hβr
  have hσ0 : ∀ u ∈ X, β u (b u) = 0 := by
    intro u hu
    have hmem : u * b u ∈ Y := by
      have h := hbY u
      rwa [mul_comm] at h
    have h1 := hq u (b u)
    rw [hqY _ hmem, hqb u, hqX u hu] at h1
    simp only [zero_add] at h1
    exact h1.symm
  have hσalt : ∀ u ∈ X, β u (b u * u) = 0 := by
    intro u hu
    rw [hβr, hβalt u, add_zero]
    exact hσ0 u hu
  have hS2 : ∀ u v w : A, β u (b (v * w) * (v * w)) = β u (b v * v) + β u (b w * w) := by
    intro u v w
    have e : b (v * w) * (v * w) = (b v * v) * (b w * w) := by
      rw [map_mul]; ac_rfl
    rw [e, hβr]
  have hS3 : ∀ u ∈ X, ∀ v ∈ X, β u (b v * v) = β v (b u * u) := by
    intro u hu v hv
    have h := hσalt (u * v) (X.mul_mem hu hv)
    rw [hβl, hS2 u u v, hS2 v u v, hσalt u hu, hσalt v hv, zero_add, add_zero] at h
    exact ndF95_eq_of_add_eq_zero h
  have hA : ∃ u ∈ X, ∃ v ∈ X, β u (b v * v) ≠ 0 := by
    obtain ⟨p, r, hpr⟩ := hβ0
    have hp : p ∈ X ⊔ Y := by rw [hXY.sup_eq_top]; exact Subgroup.mem_top p
    have hr : r ∈ X ⊔ Y := by rw [hXY.sup_eq_top]; exact Subgroup.mem_top r
    obtain ⟨x₁', hx₁', y₁', hy₁', rfl⟩ := Subgroup.mem_sup.mp hp
    obtain ⟨x₂', hx₂', y₂', hy₂', rfl⟩ := Subgroup.mem_sup.mp hr
    have hexpand : β (x₁' * y₁') (x₂' * y₂') = β x₁' y₂' + β y₁' x₂' := by
      rw [hβl, hβr, hβr, hXiso x₁' hx₁' x₂' hx₂', hYiso y₁' hy₁' y₂' hy₂', zero_add, add_zero]
    rw [hexpand] at hpr
    by_cases h1 : β x₁' y₂' = 0
    · have h2 : β y₁' x₂' ≠ 0 := fun h2 => hpr (by rw [h1, h2, add_zero])
      obtain ⟨x'', hx'', hx''eq⟩ := hsurj y₁' hy₁'
      refine ⟨x₂', hx₂', x'', hx'', ?_⟩
      rw [hx''eq, hsymm]
      exact h2
    · obtain ⟨x'', hx'', hx''eq⟩ := hsurj y₂' hy₂'
      refine ⟨x₁', hx₁', x'', hx'', ?_⟩
      rw [hx''eq]
      exact h1
  by_contra hx1
  obtain ⟨e, he, he1, hex⟩ : ∃ e ∈ X, e ≠ 1 ∧ e ≠ x₁ := by
    by_contra hcon
    have hsub : (X : Set A) ⊆ ({1, x₁} : Set A) := by
      intro t ht
      by_cases h1 : t = 1
      · simp [h1]
      · have h2 : t = x₁ := by
          by_contra h2
          exact hcon ⟨t, ht, h1, h2⟩
        simp [h2]
    have h2 := Set.ncard_le_ncard hsub
    have h3 : ({1, x₁} : Set A).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    have hXn : (X : Set A).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hX
    omega
  have hexx : e * x₁ ≠ 1 := fun h =>
    hex ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right (hexp x₁)))
  have hexne : e * x₁ ≠ e := fun h => hx1 (mul_left_cancel (h.trans (mul_one e).symm))
  have hxexne : x₁ ≠ e * x₁ := fun h => he1 (mul_right_cancel (h.symm.trans (one_mul x₁).symm))
  have hexx' : e ≠ e * x₁ := fun h => hexne h.symm
  have hx1ne : x₁ ≠ e := fun h => hex h.symm
  have n1 : (1 : A) ∉ ({x₁, e, e * x₁} : Set A) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hx1 h.symm, fun h => he1 h.symm, fun h => hexx h.symm⟩
  have n2 : x₁ ∉ ({e, e * x₁} : Set A) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1ne, hxexne⟩
  have n3 : e ∉ ({e * x₁} : Set A) := by
    simp only [Set.mem_singleton_iff]
    exact hexx'
  have hT : ({1, x₁, e, e * x₁} : Set A).ncard = 4 := by
    have c1 := Set.ncard_insert_of_notMem n3 (Set.toFinite _)
    have c2 := Set.ncard_insert_of_notMem n2 (Set.toFinite _)
    have c3 := Set.ncard_insert_of_notMem n1 (Set.toFinite _)
    have c4 := Set.ncard_singleton (e * x₁)
    omega
  have hXn : (X : Set A).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hX
  have hEnum : ∀ z ∈ X, z = 1 ∨ z = x₁ ∨ z = e ∨ z = e * x₁ := by
    intro z hz
    have hTX : ({1, x₁, e, e * x₁} : Set A) ⊆ (X : Set A) := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact X.one_mem
      · exact hx₁
      · exact he
      · exact X.mul_mem he hx₁
    have hTeq : ({1, x₁, e, e * x₁} : Set A) = (X : Set A) :=
      Set.eq_of_subset_of_ncard_le hTX (hXn.trans hT.symm).le
    have hzT : z ∈ ({1, x₁, e, e * x₁} : Set A) := by
      rw [hTeq]
      exact hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzT
  have hZe : ∀ v ∈ X, β e (b v * v) = 0 := by
    intro v hv
    rcases hEnum v hv with h | h | h | h
    · rw [h, map_one, mul_one]
      exact hβ1r e
    · rw [h, hS3 e he x₁ hx₁]
      exact hrad e he
    · rw [h]
      exact hσalt e he
    · rw [h, hS2 e e x₁, hσalt e he, zero_add, hS3 e he x₁ hx₁]
      exact hrad e he
  have hZf : ∀ v ∈ X, β (e * x₁) (b v * v) = 0 := by
    intro v hv
    rw [hβl, hZe v hv, hrad v hv, zero_add]
  have hZall : ∀ u ∈ X, ∀ v ∈ X, β u (b v * v) = 0 := by
    intro u hu v hv
    rcases hEnum u hu with h | h | h | h
    · rw [h]
      exact hβ1 _
    · rw [h]
      exact hrad v hv
    · rw [h]
      exact hZe v hv
    · rw [h]
      exact hZf v hv
  obtain ⟨u, hu, v, hv, hne⟩ := hA
  exact hne (hZall u hu v hv)

theorem nondeg_of_rad_Y {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (β : A → A → ZMod 2) (hβl : ∀ x y z, β (x * y) z = β x z + β y z)
    (hβr : ∀ x y z, β x (y * z) = β x y + β x z) (hβalt : ∀ x, β x x = 0)
    (X Y : Subgroup A) (hXY : IsCompl X Y) (hXX : ∀ x ∈ X, ∀ x' ∈ X, β x x' = 0)
    (hYY : ∀ y ∈ Y, ∀ y' ∈ Y, β y y' = 0) (hcard : Nat.card X = Nat.card Y)
    (hY : ∀ y ∈ Y, (∀ x ∈ X, β x y = 0) → y = 1) :
    ∀ x : A, (∀ y, β x y = 0) → x = 1 := by
  intro x hx
  have hxsup : x ∈ X ⊔ Y := by
    rw [hXY.sup_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Subgroup.mem_sup.mp hxsup
  have hsymm := ndF95_symm β hβl hβr hβalt
  have hy1 : y₁ = 1 := by
    apply hY y₁ hy₁
    intro x' hx'
    have h1 : β (x₁ * y₁) x' = β y₁ x' := by
      rw [hβl, hXX x₁ hx₁ x' hx', zero_add]
    rw [hsymm x' y₁, ← h1]
    exact hx x'
  subst hy1
  rw [mul_one] at hx ⊢
  have hβ1 : ∀ z, β 1 z = 0 := ndF95_zero_left β hβl
  have hβ1r : ∀ z, β z 1 = 0 := ndF95_zero_right β hβr
  letI : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule (ndF95_twoNsmul hexp X)
  letI : Module (ZMod 2) (Additive Y) := AddCommGroup.zmodModule (ndF95_twoNsmul hexp Y)
  haveI : Finite (Additive X) := inferInstanceAs (Finite X)
  haveI : Finite (Additive Y) := inferInstanceAs (Finite Y)
  have hfin : Module.finrank (ZMod 2) (Additive X) = Module.finrank (ZMod 2) (Additive Y) := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)
    rw [Nat.card_zmod] at h1 h2
    have h3 : (2 : ℕ) ^ Module.finrank (ZMod 2) (Additive X)
        = 2 ^ Module.finrank (ZMod 2) (Additive Y) := by
      rw [← h1, ← h2]
      exact hcard
    exact Nat.pow_right_injective (le_refl 2) h3
  let B : Additive X →ₗ[ZMod 2] Additive Y →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.mk₂ (ZMod 2)
      (fun v w => β ((Additive.toMul v : X) : A) ((Additive.toMul w : Y) : A))
      (fun v₁ v₂ w => hβl ((Additive.toMul v₁ : X) : A) ((Additive.toMul v₂ : X) : A)
        ((Additive.toMul w : Y) : A))
      (fun c v w => by
        rcases ndF95_cases c with rfl | rfl
        · rw [zero_smul, zero_smul]
          exact hβ1 _
        · rw [one_smul, one_smul])
      (fun v w₁ w₂ => hβr ((Additive.toMul v : X) : A) ((Additive.toMul w₁ : Y) : A)
        ((Additive.toMul w₂ : Y) : A))
      (fun c v w => by
        rcases ndF95_cases c with rfl | rfl
        · rw [zero_smul, zero_smul]
          exact hβ1r _
        · rw [one_smul, one_smul])
  have hW : ∀ w : Additive Y, (∀ v : Additive X, B v w = 0) → w = 0 := by
    intro w hw
    have hy : ((Additive.toMul w : Y) : A) = 1 := by
      apply hY _ (Additive.toMul w : Y).2
      intro x' hx'
      exact hw (Additive.ofMul (⟨x', hx'⟩ : X))
    exact Additive.toMul.injective (Subtype.ext hy)
  have hx0 : (Additive.ofMul (⟨x₁, hx₁⟩ : X) : Additive X) = 0 :=
    ndF95_leftTrivial B hfin hW _ (fun w => hx ((Additive.toMul w : Y) : A))
  exact congrArg (fun z : Additive X => ((Additive.toMul z : X) : A)) hx0

theorem nondeg_dim_two {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (q : A → ZMod 2) (β : A → A → ZMod 2)
    (hβl : ∀ x y z, β (x * y) z = β x z + β y z) (hβr : ∀ x y z, β x (y * z) = β x y + β x z)
    (hq : ∀ x y, q (x * y) = q x + q y + β x y) (hβalt : ∀ x, β x x = 0)
    (a b : A ≃* A) (ha : ∀ x, a (a x) = x) (hb : ∀ x, b (b x) = x)
    (hqa : ∀ x, q (a x) = q x) (hqb : ∀ x, q (b x) = q x)
    (X Y : Subgroup A) (hXa : ∀ x, x ∈ X ↔ a x = x) (hYb : ∀ y, y ∈ Y ↔ b y = y)
    (haX : ∀ x, a x * x ∈ X) (hbY : ∀ y, b y * y ∈ Y)
    (hXY : IsCompl X Y) (hqX : ∀ x ∈ X, q x = 0) (hqY : ∀ y ∈ Y, q y = 0)
    (hX : Nat.card X = 4) (hβ0 : ∃ x y, β x y ≠ 0) :
    ∀ x : A, (∀ y, β x y = 0) → x = 1 := by
  have hcardY : Nat.card Y = 4 := by
    have h1 := ndF95_cardLe hexp b X Y hXY hYb hbY
    have h2 := ndF95_cardLe hexp a Y X hXY.symm hXa haX
    omega
  intro x hx
  have hxsup : x ∈ X ⊔ Y := by
    rw [hXY.sup_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Subgroup.mem_sup.mp hxsup
  have hx1 : x₁ = 1 := by
    apply ndF95_radX hexp q β hβl hβr hq hβalt b hqb X Y hYb hbY hXY hqX hqY hX hcardY hβ0 x₁ hx₁
    intro x'' _
    have h1 := hx (b x'' * x'')
    rw [hβl, ndF95_iso q β hq Y hqY y₁ (b x'' * x'') hy₁ (hbY x''), add_zero] at h1
    exact h1
  subst hx1
  rw [one_mul] at hx ⊢
  exact ndF95_radX hexp q β hβl hβr hq hβalt a hqa Y X hXa haX hXY.symm hqY hqX hcardY hX hβ0
    y₁ hy₁ (fun x'' _ => hx (a x'' * x''))

end CFSG.Quasithin.RonanF95
