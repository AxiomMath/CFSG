module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace OddFrame

structure OddPrime (ℓ : ℕ) : Prop where
  prime : ℓ.Prime
  ne_two : ℓ ≠ 2
  fermat : ∀ r : ℕ, r.Prime → r ∣ ℓ - 1 → r = 2

theorem OddPrime.of_three_or_five {ℓ : ℕ} (h : ℓ = 3 ∨ ℓ = 5) : OddPrime ℓ := by
  rcases h with rfl | rfl
  · refine ⟨by norm_num, by norm_num, fun r hr hrd => ?_⟩
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (by simpa using hrd)
  · refine ⟨by norm_num, by norm_num, fun r hr hrd => ?_⟩
    have h4 : r ∣ 2 ^ 2 := by simpa using hrd
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4)

variable {ℓ : ℕ}

theorem OddPrime.odd (h : OddPrime ℓ) : Odd ℓ := h.prime.odd_of_ne_two h.ne_two

theorem OddPrime.three_le (h : OddPrime ℓ) : 3 ≤ ℓ := by
  have := h.prime.two_le
  have := h.ne_two
  omega

theorem OddPrime.two_dvd (h : OddPrime ℓ) : 2 ∣ ℓ - 1 := by
  obtain ⟨k, hk⟩ := h.odd
  exact ⟨k, by omega⟩

theorem OddPrime.not_dvd (h : OddPrime ℓ) : ¬ ℓ ∣ ℓ - 1 := by
  have h3 := h.three_le
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  omega

variable {X : Type*} [Group X]

theorem inv_of_involution {τ : MulAut X} (hτ : ∀ x, τ (τ x) = x) (W : Subgroup X) [Finite W]
    (hW : ∀ w ∈ W, τ w ∈ W) (hfix : ∀ w ∈ W, τ w = w → w = 1) (w : X) (hw : w ∈ W) :
    τ w = w⁻¹ := by
  let φ : W → W := fun z => ⟨(z : X)⁻¹ * τ z, W.mul_mem (W.inv_mem z.2) (hW z z.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h : (a : X)⁻¹ * τ a = (b : X)⁻¹ * τ b := congrArg Subtype.val hab
    have h1 : (b : X) * (a : X)⁻¹ * τ a = τ b := by
      calc (b : X) * (a : X)⁻¹ * τ a = (b : X) * ((a : X)⁻¹ * τ a) := by rw [mul_assoc]
        _ = (b : X) * ((b : X)⁻¹ * τ b) := by rw [h]
        _ = τ b := by rw [mul_inv_cancel_left]
    have h2 : τ ((b : X) * (a : X)⁻¹) = (b : X) * (a : X)⁻¹ := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel_right]
    have h3 := hfix ((b : X) * (a : X)⁻¹) (W.mul_mem b.2 (W.inv_mem a.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3).symm
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hinj ⟨w, hw⟩
  have hz' : (z : X)⁻¹ * τ z = w := congrArg Subtype.val hz
  rw [← hz', map_mul, map_inv, hτ, mul_inv_rev, inv_inv]

theorem commute_of_inv {τ : MulAut X} {W : Subgroup X} (hinv : ∀ w ∈ W, τ w = w⁻¹) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  have h1 := hinv (a * b) (W.mul_mem ha hb)
  rw [map_mul, hinv a ha, hinv b hb, mul_inv_rev] at h1
  have h2 := congrArg Inv.inv h1
  simp only [mul_inv_rev, inv_inv] at h2
  exact h2.symm

theorem exists_normal_zpowers [Finite X] (hℓ : OddPrime ℓ) {C : Subgroup X}
    (hcard : Nat.card C = ℓ * (ℓ - 1)) :
    ∃ c ∈ C, orderOf c = ℓ ∧ ∀ y ∈ C, y * c * y⁻¹ ∈ Subgroup.zpowers c := by
  have := Fact.mk hℓ.prime
  obtain ⟨S⟩ : Nonempty (Sylow ℓ C) := inferInstance
  have h3 := hℓ.three_le
  have hS : Nat.card S = ℓ := by
    rw [Sylow.card_eq_multiplicity, hcard,
      Nat.factorization_mul hℓ.prime.ne_zero (by omega : ℓ - 1 ≠ 0), Finsupp.add_apply,
      hℓ.prime.factorization_self, Nat.factorization_eq_zero_of_not_dvd hℓ.not_dvd, add_zero,
      pow_one]
  have hidx : (S : Subgroup C).index = ℓ - 1 := by
    have := (S : Subgroup C).card_mul_index
    rw [hS, hcard] at this
    exact Nat.eq_of_mul_eq_mul_left hℓ.prime.pos this
  have hn : Nat.card (Sylow ℓ C) = 1 := by
    have hmod := card_sylow_modEq_one ℓ C
    have hdvd : Nat.card (Sylow ℓ C) ∣ ℓ - 1 := hidx ▸ Sylow.card_dvd_index S
    have hle : Nat.card (Sylow ℓ C) ≤ ℓ - 1 := Nat.le_of_dvd (by omega) hdvd
    have hpos : 0 < Nat.card (Sylow ℓ C) := Nat.card_pos
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt (by omega : Nat.card (Sylow ℓ C) < ℓ),
      Nat.mod_eq_of_lt (by omega : 1 < ℓ)] at hmod
    exact hmod
  have : Subsingleton (Sylow ℓ C) := (Nat.card_eq_one_iff_unique.mp hn).1
  have hSn : (S : Subgroup C).Normal := Sylow.normal_of_subsingleton S
  have : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := S)
  have hgord : orderOf g = ℓ := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hS]
  refine ⟨((g : C) : X), (g : C).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hgord]
  · intro y hy
    have hmem : (⟨y, hy⟩ : C) * (g : C) * (⟨y, hy⟩ : C)⁻¹ ∈ (S : Subgroup C) :=
      hSn.conj_mem _ g.2 _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, hmem⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg (fun z : S => (((z : C)) : X)) hk
    simpa using this

theorem eq_one_of_commute_of_odd {u v : X}
    (hu : IsPGroup 2 (Subgroup.centralizer ({u} : Set X)))
    (hv : Odd (orderOf v)) (huv : u * v = v * u) : v = 1 := by
  have hmem : v ∈ Subgroup.centralizer ({u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr huv.symm
  obtain ⟨k, hk⟩ := hu ⟨v, hmem⟩
  have hd : orderOf v ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hv
    exact (Nat.not_even_iff_odd.mpr hv) (even_two.pow_of_ne_zero hne)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem odd_orderOf_of_odd_card [Finite X] {W : Subgroup X} (hodd : Odd (Nat.card W)) {w : X}
    (hw : w ∈ W) : Odd (orderOf w) := by
  have h := orderOf_dvd_natCard (⟨w, hw⟩ : W)
  rw [Subgroup.orderOf_mk] at h
  exact hodd.of_dvd_nat h

theorem odd_card_of_no_involution [Finite X] {W : Subgroup X}
    (h : ∀ w ∈ W, orderOf w ≠ 2) : Odd (Nat.card W) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card W := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2
  exact h g g.2 (by rw [Subgroup.orderOf_coe, hg])

structure Core (ℓ : ℕ) (C : Subgroup X) (c t : X) : Prop where
  odd : OddPrime ℓ
  invCent : ∀ u : X, orderOf u = 2 → IsPGroup 2 (Subgroup.centralizer ({u} : Set X))
  card : Nat.card C = ℓ * (ℓ - 1)
  mem_c : c ∈ C
  ord_c : orderOf c = ℓ
  norm : ∀ y ∈ C, y * c * y⁻¹ ∈ Subgroup.zpowers c
  mem_t : t ∈ C
  ord_t : orderOf t = 2

variable {C : Subgroup X} {c t : X}

theorem Core.odd_orderOf_c (h : Core ℓ C c t) : Odd (orderOf c) := h.ord_c ▸ h.odd.odd

theorem Core.c_ne_one (h : Core ℓ C c t) : c ≠ 1 := by
  intro h1
  have h3 := h.odd.three_le
  have := h.ord_c
  rw [h1, orderOf_one] at this
  omega

theorem Core.tt (h : Core ℓ C c t) : t * t = 1 := by
  simpa [h.ord_t, pow_two] using pow_orderOf_eq_one t

theorem Core.zpowers_card (h : Core ℓ C c t) : Nat.card (Subgroup.zpowers c) = ℓ := by
  rw [Nat.card_zpowers, h.ord_c]

theorem Core.not_commute_c [Finite X] (h : Core ℓ C c t) {u : X} (hu : orderOf u = 2)
    (huc : u * c = c * u) : False :=
  h.c_ne_one (eq_one_of_commute_of_odd (h.invCent u hu) h.odd_orderOf_c huc)

theorem Core.conj_t [Finite X] (h : Core ℓ C c t) : t * c * t⁻¹ = c⁻¹ := by
  have hpr := h.odd.prime
  have htt := h.tt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.norm t h.mem_t)
  have h2 : c ^ (k * k) = c := by
    have e1 : t * (t * c * t⁻¹) * t⁻¹ = c := by
      rw [hti, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
    calc c ^ (k * k) = (c ^ k) ^ k := zpow_mul c k k
      _ = (t * c * t⁻¹) ^ k := by rw [hk]
      _ = t * c ^ k * t⁻¹ := conj_zpow
      _ = t * (t * c * t⁻¹) * t⁻¹ := by rw [hk]
      _ = c := e1
  have h3 : (ℓ : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← h.ord_c, orderOf_dvd_iff_zpow_eq_one]
    have : (k - 1) * (k + 1) = k * k - 1 := by ring
    rw [this, zpow_sub_one, h2, mul_inv_cancel]
  rcases (Nat.prime_iff_prime_int.mp hpr).dvd_or_dvd h3 with h4 | h4
  · exfalso
    rw [← h.ord_c, orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, mul_inv_eq_one] at h4
    rw [h4] at hk
    have : t * c = c * t := by
      have := congrArg (· * t) hk.symm
      simpa [mul_assoc] using this
    exact h.not_commute_c h.ord_t this
  · rw [← h.ord_c, orderOf_dvd_iff_zpow_eq_one, zpow_add_one] at h4
    rw [← hk]
    exact eq_inv_of_mul_eq_one_left h4

theorem Core.eq_zpowers_of_no_involution [Finite X] (h : Core ℓ C c t) {D : Subgroup X}
    (hDC : D ≤ C) (hcD : c ∈ D) (hno : ∀ u ∈ D, orderOf u ≠ 2) : D = Subgroup.zpowers c := by
  have hℓ := h.odd
  have hPD : Subgroup.zpowers c ≤ D := Subgroup.zpowers_le.mpr hcD
  obtain ⟨j, hj⟩ : ℓ ∣ Nat.card D := h.zpowers_card ▸ Subgroup.card_dvd_of_le hPD
  have h2 : Nat.card D ∣ ℓ * (ℓ - 1) := h.card ▸ Subgroup.card_dvd_of_le hDC
  rw [hj] at h2
  have hjd : j ∣ ℓ - 1 := Nat.dvd_of_mul_dvd_mul_left hℓ.prime.pos h2
  by_cases hj1 : j = 1
  · refine (Subgroup.eq_of_le_of_card_ge hPD ?_).symm
    rw [hj, hj1, mul_one, h.zpowers_card]
  · exfalso
    obtain ⟨r, hr, hrj⟩ := Nat.exists_prime_and_dvd hj1
    have hr2 : r = 2 := hℓ.fermat r hr (hrj.trans hjd)
    subst hr2
    have h2D : 2 ∣ Nat.card D := hj ▸ hrj.mul_left ℓ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2D
    exact hno u u.2 (by rw [Subgroup.orderOf_coe, hu])

theorem Core.mem_zpowers_of_commute [Finite X] (h : Core ℓ C c t) {v : X} (hv : v ∈ C)
    (hvc : v * c = c * v) : v ∈ Subgroup.zpowers c := by
  have hD : C ⊓ Subgroup.centralizer ({c} : Set X) = Subgroup.zpowers c := by
    refine h.eq_zpowers_of_no_involution inf_le_left
      (Subgroup.mem_inf.mpr ⟨h.mem_c, Subgroup.mem_centralizer_iff.mpr (by simp)⟩) ?_
    intro u hu hu2
    exact h.not_commute_c hu2 (Subgroup.mem_centralizer_singleton_iff.mp hu.2)
  rw [← hD]
  exact Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hvc⟩

theorem Core.conj_inv_of_odd [Finite X] (h : Core ℓ C c t) {W : Subgroup X}
    (hodd : Odd (Nat.card W)) (hW : ∀ w ∈ W, t * w * t⁻¹ ∈ W) :
    ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ := by
  have htt := h.tt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine fun w hw => inv_of_involution (τ := MulAut.conj t) (fun x => ?_) W hW ?_ w hw
  · simp only [MulAut.conj_apply, hti]
    rw [← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  · intro w hw hfix
    refine eq_one_of_commute_of_odd (h.invCent t h.ord_t) (odd_orderOf_of_odd_card hodd hw) ?_
    have hfix' : t * w * t⁻¹ = w := hfix
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w * t := by rw [hfix']

theorem card_le_of_pgroup {p n : ℕ} [Fact p.Prime] {Q : Subgroup X} [Finite Q]
    (hQ : IsPGroup p Q) (hdvd : Nat.card Q ∣ n) (hn : ¬ p ^ 2 ∣ n) : Nat.card Q ≤ p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra hk1
    have h1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : k ≤ 1)
    rw [pow_one] at h1
    exact hlt (hk ▸ h1)
  rw [hk] at hdvd
  exact hn ((pow_dvd_pow p hk2).trans hdvd)

abbrev Core.Z (c : X) : Subgroup X := Subgroup.centralizer ({c} : Set X)

theorem Core.mem_Z {c z : X} : z ∈ Core.Z c ↔ z * c = c * z :=
  Subgroup.mem_centralizer_singleton_iff

theorem Core.odd_card_Z [Finite X] (h : Core ℓ C c t) : Odd (Nat.card (Core.Z c)) :=
  odd_card_of_no_involution fun _ hw hw2 => h.not_commute_c hw2 (Core.mem_Z.mp hw)

theorem Core.odd_orderOf_of_mem_Z [Finite X] (h : Core ℓ C c t) {z : X} (hz : z ∈ Core.Z c) :
    Odd (orderOf z) :=
  odd_orderOf_of_odd_card h.odd_card_Z hz

theorem Core.commute_zpowers {c z x : X} (hz : z ∈ Core.Z c) (hx : x ∈ Subgroup.zpowers c) :
    z * x = x * z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_right (Core.mem_Z.mp hz) k).eq

theorem centralizer_zpowers_eq (c : X) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup X) : Set X) = Core.Z c := by
  ext z
  rw [Subgroup.mem_centralizer_iff, Core.mem_Z]
  constructor
  · intro hz
    exact (hz c (Subgroup.mem_zpowers c)).symm
  · intro hz x hx
    exact (Core.commute_zpowers (Core.mem_Z.mpr hz) hx).symm

theorem conj_mem_zpowers_of_conj {c y : X} (hy : y * c * y⁻¹ ∈ Subgroup.zpowers c) {x : X}
    (hx : x ∈ Subgroup.zpowers c) : y * x * y⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hy k

theorem le_normalizer_of_conj {c : X} {H : Subgroup X}
    (hH : ∀ y ∈ H, y * c * y⁻¹ ∈ Subgroup.zpowers c) :
    H ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup X) : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_zpowers_of_conj (hH y hy), fun hx => ?_⟩
  have := conj_mem_zpowers_of_conj (hH y⁻¹ (Subgroup.inv_mem _ hy)) hx
  simpa [mul_assoc] using this

theorem Core.le_normalizer (h : Core ℓ C c t) :
    C ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup X) : Set X) :=
  le_normalizer_of_conj h.norm

theorem Core.conj_mem_Z_of_mem [Finite X] (h : Core ℓ C c t) {y z : X} (hy : y ∈ C)
    (hz : z ∈ Core.Z c) : y * z * y⁻¹ ∈ Core.Z c := by
  have hd : y⁻¹ * c * y ∈ Subgroup.zpowers c := by
    simpa using h.norm y⁻¹ (Subgroup.inv_mem _ hy)
  have hzd := Core.commute_zpowers hz hd
  rw [Core.mem_Z]
  calc y * z * y⁻¹ * c = y * (z * (y⁻¹ * c * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * c * y) * z) * y⁻¹ := by rw [hzd]
    _ = c * (y * z * y⁻¹) := by group

theorem Core.conj_inv_Z [Finite X] (h : Core ℓ C c t) {z : X} (hz : z ∈ Core.Z c) :
    t * z * t⁻¹ = z⁻¹ :=
  h.conj_inv_of_odd h.odd_card_Z (fun _ hw => h.conj_mem_Z_of_mem h.mem_t hw) z hz

theorem Core.comm_Z [Finite X] (h : Core ℓ C c t) {a b : X} (ha : a ∈ Core.Z c)
    (hb : b ∈ Core.Z c) : a * b = b * a :=
  commute_of_inv (τ := MulAut.conj t) (W := Core.Z c) (fun _ hw => h.conj_inv_Z hw) a ha b hb

theorem Core.zpowers_isPGroup (h : Core ℓ C c t) : IsPGroup ℓ (Subgroup.zpowers c) := by
  have := Fact.mk h.odd.prime
  exact IsPGroup.of_card (n := 1) (by rw [h.zpowers_card, pow_one])

theorem Core.zpowers_le (h : Core ℓ C c t) : Subgroup.zpowers c ≤ C :=
  Subgroup.zpowers_le.mpr h.mem_c

theorem Core.eq_zpowers_of_pgroup [Finite X] (h : Core ℓ C c t) {Q : Subgroup X}
    (hQ : IsPGroup ℓ Q) (hQC : Q ≤ C) (hcQ : c ∈ Q) : Q = Subgroup.zpowers c := by
  have := Fact.mk h.odd.prime
  have hn : ¬ ℓ ^ 2 ∣ Nat.card C := by
    rw [h.card, pow_two]
    intro hd
    exact h.odd.not_dvd ((Nat.mul_dvd_mul_iff_left h.odd.prime.pos).mp hd)
  have hle := card_le_of_pgroup hQ (Subgroup.card_dvd_of_le hQC) hn
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcQ)
    (by rw [h.zpowers_card]; exact hle)).symm

theorem Core.mem_zpowers_of_orderOf [Finite X] (h : Core ℓ C c t) {u : X} (hu : u ∈ C)
    (hord : orderOf u = ℓ) : u ∈ Subgroup.zpowers c := by
  have := Fact.mk h.odd.prime
  have hup : IsPGroup ℓ (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hsup := IsPGroup.to_sup_of_normal_left' h.zpowers_isPGroup hup
    (Subgroup.zpowers_le.mpr (h.le_normalizer hu))
  have heq := h.eq_zpowers_of_pgroup hsup (sup_le h.zpowers_le (Subgroup.zpowers_le.mpr hu))
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)

theorem Core.fpf [Finite X] (h : Core ℓ C c t) {v z : X} (hv : v ∈ C)
    (hvP : v ∉ Subgroup.zpowers c) (hz : z ∈ Core.Z c) (hvz : v * z = z * v) : z = 1 := by
  have hℓ := h.odd
  have hm : orderOf v ∣ ℓ * (ℓ - 1) := by
    have := orderOf_dvd_natCard (⟨v, hv⟩ : C)
    rwa [Subgroup.orderOf_mk, h.card] at this
  have hv1 : v ≠ 1 := fun h1 => hvP (h1 ▸ Subgroup.one_mem _)
  have hm1 : orderOf v ≠ 1 := fun h1 => hv1 (orderOf_eq_one_iff.mp h1)
  have hmpos : 0 < orderOf v := orderOf_pos v
  have hℓm : ¬ ℓ ∣ orderOf v := by
    intro hdvd
    have hu : orderOf (v ^ (orderOf v / ℓ)) = ℓ :=
      orderOf_pow_orderOf_div hmpos.ne' hdvd
    have huC : v ^ (orderOf v / ℓ) ∈ C := Subgroup.pow_mem _ hv _
    have huP := h.mem_zpowers_of_orderOf huC hu
    have hPu : Subgroup.zpowers (v ^ (orderOf v / ℓ)) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huP) ?_
      rw [h.zpowers_card, Nat.card_zpowers, hu]
    have hcu : c ∈ Subgroup.zpowers (v ^ (orderOf v / ℓ)) := hPu ▸ Subgroup.mem_zpowers c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcu
    have hvc : v * c = c * v := by
      rw [← hk]
      exact (((Commute.refl v).pow_right (orderOf v / ℓ)).zpow_right k).eq
    exact hvP (h.mem_zpowers_of_commute hv hvc)
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
  have hr2 : r = 2 := by
    rcases (Nat.Prime.dvd_mul hr).mp (hrm.trans hm) with hd | hd
    · exact absurd (((Nat.prime_dvd_prime_iff_eq hr hℓ.prime).mp hd) ▸ hrm) hℓm
    · exact hℓ.fermat r hr hd
  subst hr2
  have hw : orderOf (v ^ (orderOf v / 2)) = 2 := orderOf_pow_orderOf_div hmpos.ne' hrm
  have hzw : (v ^ (orderOf v / 2)) * z = z * (v ^ (orderOf v / 2)) :=
    ((Commute.pow_left (show Commute v z from hvz) (orderOf v / 2))).eq
  exact eq_one_of_commute_of_odd (h.invCent _ hw) (h.odd_orderOf_of_mem_Z hz) hzw

theorem Core.exists_conj_eq [Finite X] (h : Core ℓ C c t) {g : X}
    (hg : g ∈ Subgroup.zpowers c) (hg1 : g ≠ 1) : ∃ y ∈ C, y * c * y⁻¹ = g := by
  have hℓ := h.odd
  let act : C →* MulAut X := (MulAut.conj : X →* MulAut X).comp C.subtype
  let : MulAction C X := MulAction.compHom X act
  have hsmul : ∀ (y : C) (x : X), y • x = (y : X) * x * (y : X)⁻¹ := fun y x => rfl
  have hstab : MulAction.stabilizer C c = (Subgroup.zpowers c).subgroupOf C := by
    ext y
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      refine h.mem_zpowers_of_commute y.2 ?_
      calc (y : X) * c = (y : X) * c * (y : X)⁻¹ * (y : X) := by group
        _ = c * y := by rw [hy]
    · intro hy
      have : (y : X) * c = c * y := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← hk]
        exact ((Commute.refl c).zpow_left k).eq
      rw [this]
      group
  have hcardstab : Nat.card (MulAction.stabilizer C c) = ℓ := by
    rw [hstab, ← h.zpowers_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.zpowers_le).toEquiv
  have hindex : (MulAction.stabilizer C c).index = ℓ - 1 := by
    have := (MulAction.stabilizer C c).card_mul_index
    rw [hcardstab, h.card] at this
    exact Nat.eq_of_mul_eq_mul_left hℓ.prime.pos this
  have horbit : (MulAction.orbit C c).ncard = ℓ - 1 := by
    rw [← MulAction.index_stabilizer C c, hindex]
  have hsub : MulAction.orbit C c ⊆ ((Subgroup.zpowers c : Subgroup X) : Set X) \ {1} := by
    rintro _ ⟨y, rfl⟩
    show y • c ∈ _
    rw [hsmul]
    refine ⟨h.norm y y.2, fun h1 => h.c_ne_one ?_⟩
    have : (y : X) * c * (y : X)⁻¹ = 1 := h1
    simpa using this
  have hncard : (((Subgroup.zpowers c : Subgroup X) : Set X) \ {1}).ncard = ℓ - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) h.zpowers_card
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, horbit])
  have hgmem : g ∈ MulAction.orbit C c :=
    heq ▸ (⟨hg, hg1⟩ : g ∈ ((Subgroup.zpowers c : Subgroup X) : Set X) \ {1})
  obtain ⟨y, hy⟩ := hgmem
  exact ⟨y, y.2, (hsmul y c).symm.trans hy⟩

theorem Core.normalizer_decomp [Finite X] (h : Core ℓ C c t) {x : X}
    (hx : x ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup X) : Set X)) :
    ∃ z ∈ Core.Z c, ∃ y ∈ C, x = z * y := by
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hx c).mp (Subgroup.mem_zpowers c)
  have hne : x * c * x⁻¹ ≠ 1 := fun h1 => h.c_ne_one (by simpa using h1)
  obtain ⟨y, hy, hyc⟩ := h.exists_conj_eq hxc hne
  have hz : y⁻¹ * x ∈ Core.Z c := by
    rw [Core.mem_Z]
    calc y⁻¹ * x * c = y⁻¹ * (x * c * x⁻¹) * x := by group
      _ = y⁻¹ * (y * c * y⁻¹) * x := by rw [hyc]
      _ = c * (y⁻¹ * x) := by group
  exact ⟨y * (y⁻¹ * x) * y⁻¹, h.conj_mem_Z_of_mem hy hz, y, hy, by group⟩

theorem Core.zpowers_le_of_normal [Finite X] (h : Core ℓ C c t) {N : Subgroup X} (hNC : N ≤ C)
    (hN : ∀ n ∈ N, ∀ y ∈ C, y * n * y⁻¹ ∈ N) (hbot : N ≠ ⊥) : Subgroup.zpowers c ≤ N := by
  have := Fact.mk h.odd.prime
  by_contra hnle
  apply hbot
  have hdvd : Nat.card (N ⊓ Subgroup.zpowers c : Subgroup X) ∣ ℓ :=
    h.zpowers_card ▸ Subgroup.card_dvd_of_le inf_le_right
  have hinf : N ⊓ Subgroup.zpowers c = ⊥ := by
    rcases (Nat.dvd_prime h.odd.prime).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      refine hnle (inf_eq_right.mp (Subgroup.eq_of_le_of_card_ge inf_le_right ?_))
      rw [h1, h.zpowers_card]
  refine eq_bot_iff.mpr fun m hm => ?_
  have hmC : m ∈ C := hNC hm
  have h1 : m * c * m⁻¹ * c⁻¹ ∈ N ⊓ Subgroup.zpowers c := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := Subgroup.mul_mem N hm (hN m⁻¹ (Subgroup.inv_mem _ hm) c h.mem_c)
      simpa [mul_assoc] using this
    · exact Subgroup.mul_mem _ (h.norm m hmC) (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  rw [hinf, Subgroup.mem_bot] at h1
  have hcomm : m * c = c * m := by
    calc m * c = m * c * m⁻¹ * c⁻¹ * (c * m) := by group
      _ = c * m := by rw [h1, one_mul]
  have hmP := h.mem_zpowers_of_commute hmC hcomm
  have : m ∈ N ⊓ Subgroup.zpowers c := Subgroup.mem_inf.mpr ⟨hm, hmP⟩
  rw [hinf] at this
  exact this

theorem Core.commutator_mem [Finite X] (h : Core ℓ C c t) {y x : X} (hy : y ∈ C) (hx : x ∈ C) :
    y * x * y⁻¹ * x⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (h.norm y hy)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (h.norm x hx)
  have e1 : (y * x) * c * (y * x)⁻¹ = c ^ (a * b) := by
    calc (y * x) * c * (y * x)⁻¹ = y * (x * c * x⁻¹) * y⁻¹ := by group
      _ = y * c ^ b * y⁻¹ := by rw [← hb]
      _ = (y * c * y⁻¹) ^ b := conj_zpow.symm
      _ = c ^ (a * b) := by rw [← ha, ← zpow_mul]
  have e2 : (x * y) * c * (x * y)⁻¹ = c ^ (a * b) := by
    calc (x * y) * c * (x * y)⁻¹ = x * (y * c * y⁻¹) * x⁻¹ := by group
      _ = x * c ^ a * x⁻¹ := by rw [← ha]
      _ = (x * c * x⁻¹) ^ a := conj_zpow.symm
      _ = c ^ (b * a) := by rw [← hb, ← zpow_mul]
      _ = c ^ (a * b) := by rw [mul_comm]
  have hw : (x * y)⁻¹ * (y * x) ∈ Subgroup.zpowers c := by
    refine h.mem_zpowers_of_commute
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx hy))
        (Subgroup.mul_mem _ hy hx)) ?_
    calc (x * y)⁻¹ * (y * x) * c = (x * y)⁻¹ * ((y * x) * c * (y * x)⁻¹) * (y * x) := by group
      _ = (x * y)⁻¹ * ((x * y) * c * (x * y)⁻¹) * (y * x) := by rw [e1, e2]
      _ = c * ((x * y)⁻¹ * (y * x)) := by group
  have hv : x * y ∈ C := Subgroup.mul_mem _ hx hy
  have := conj_mem_zpowers_of_conj (h.norm (x * y) hv) hw
  have e3 : x * y * ((x * y)⁻¹ * (y * x)) * (x * y)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
  rwa [e3] at this

theorem exists_normal_pgroup_of_solvable [Finite X] {H : Subgroup X} [Group.IsSolvable H]
    (hne : H ≠ ⊥) : ∃ r : ℕ, r.Prime ∧ ∃ N : Subgroup X, N ≤ H ∧ N ≠ ⊥ ∧ IsPGroup r N ∧
      ∀ y ∈ H, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hF : CFSG.fittingSubgroup H ≠ ⊥ := fun hF =>
    (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
      ((CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable H).mp hF)
  rw [CFSG.fitting_eq_sup_pCore H] at hF
  obtain ⟨p, hp⟩ : ∃ p : (Nat.card H).primeFactors.attach, CFSG.pCore p.1.1 H ≠ ⊥ := by
    by_contra hall
    push Not at hall
    exact hF (iSup_eq_bot.mpr hall)
  have hpr : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  refine ⟨p.1.1, hpr, (CFSG.pCore p.1.1 H).map H.subtype, Subgroup.map_subtype_le _, ?_,
    (CFSG.pCore_isPGroup).map H.subtype, ?_⟩
  · intro hb
    exact hp ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb)
  · intro y hy n hn
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    exact ⟨⟨y, hy⟩ * m * ⟨y, hy⟩⁻¹, CFSG.pCore_normal.conj_mem m hm ⟨y, hy⟩, rfl⟩

theorem Core.le_Z_of_odd_normal [Finite X] (h : Core ℓ C c t) {N : Subgroup X}
    (hodd : Odd (Nat.card N)) (htN : ∀ w ∈ N, t * w * t⁻¹ ∈ N)
    (hcN : ∀ w ∈ N, c * w * c⁻¹ ∈ N) : N ≤ Core.Z c := by
  intro a ha
  have hinv := h.conj_inv_of_odd hodd htN
  have h1 := hinv a ha
  have h2 := hinv _ (hcN a ha)
  have h3 : t * (c * a * c⁻¹) * t⁻¹ = c⁻¹ * a⁻¹ * c := by
    calc t * (c * a * c⁻¹) * t⁻¹ = (t * c * t⁻¹) * (t * a * t⁻¹) * (t * c * t⁻¹)⁻¹ := by group
      _ = c⁻¹ * a⁻¹ * c := by rw [h.conj_t, h1]; group
  rw [h3, mul_inv_rev, mul_inv_rev, inv_inv] at h2
  have h4 : a⁻¹ * (c * c) = (c * c) * a⁻¹ := by
    calc a⁻¹ * (c * c) = c * (c⁻¹ * a⁻¹ * c) * c := by group
      _ = c * (c * (a⁻¹ * c⁻¹)) * c := by rw [h2]
      _ = (c * c) * a⁻¹ := by group
  have h5 : Commute (c * c) a :=
    (Commute.inv_left_iff.mp (show Commute a⁻¹ (c * c) from h4)).symm
  obtain ⟨m, hm⟩ := h.odd.odd
  have hcm : c = (c * c) ^ (m + 1) := by
    have hℓc := pow_orderOf_eq_one c
    rw [h.ord_c] at hℓc
    calc c = c ^ ℓ * c := by rw [hℓc, one_mul]
      _ = (c * c) ^ (m + 1) := by rw [← sq, ← pow_mul, hm, ← pow_succ]; congr 1
  rw [Core.mem_Z]
  have h6 : Commute c a := by
    rw [hcm]
    exact h5.pow_left (m + 1)
  exact h6.symm.eq

theorem Core.commute_c_of_commute [Finite X] (h : Core ℓ C c t) {n y : X} (hn : n ∈ Core.Z c)
    (hn1 : n ≠ 1) (hy : y * n = n * y) : y * c = c * y := by
  have hnodd := h.odd_orderOf_of_mem_Z hn
  have hodd : Odd (Nat.card (Subgroup.centralizer ({n} : Set X))) :=
    odd_card_of_no_involution fun w hw hw2 =>
      hn1 (eq_one_of_commute_of_odd (h.invCent w hw2) hnodd
        (Subgroup.mem_centralizer_singleton_iff.mp hw))
  have hnt : t * n * t⁻¹ = n⁻¹ := h.conj_inv_Z hn
  have hW : ∀ w ∈ Subgroup.centralizer ({n} : Set X),
      t * w * t⁻¹ ∈ Subgroup.centralizer ({n} : Set X) := by
    intro w hw
    have hw' : w * n = n * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    have h1 : (t * w * t⁻¹) * n⁻¹ = n⁻¹ * (t * w * t⁻¹) := by
      calc (t * w * t⁻¹) * n⁻¹ = (t * w * t⁻¹) * (t * n * t⁻¹) := by rw [hnt]
        _ = t * (w * n) * t⁻¹ := by group
        _ = t * (n * w) * t⁻¹ := by rw [hw']
        _ = (t * n * t⁻¹) * (t * w * t⁻¹) := by group
        _ = n⁻¹ * (t * w * t⁻¹) := by rw [hnt]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.inv_right_iff.mp (show Commute (t * w * t⁻¹) n⁻¹ from h1))
  have hcomm := commute_of_inv (τ := MulAut.conj t) (W := Subgroup.centralizer ({n} : Set X))
    (fun w hw => h.conj_inv_of_odd hodd hW w hw)
  have hyY : y ∈ Subgroup.centralizer ({n} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hcY : c ∈ Subgroup.centralizer ({n} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Core.mem_Z.mp hn).symm
  exact hcomm y hyY c hcY

theorem Core.sylow_max [Finite X] (h : Core ℓ C c t) (hℓ2 : ¬ ℓ ^ 2 ∣ Nat.card X)
    {Q : Subgroup X} (hQ : IsPGroup ℓ Q) (hcQ : Subgroup.zpowers c ≤ Q) :
    Q = Subgroup.zpowers c := by
  have := Fact.mk h.odd.prime
  have hle := card_le_of_pgroup hQ (Subgroup.card_subgroup_dvd_card Q) hℓ2
  exact (Subgroup.eq_of_le_of_card_ge hcQ (by rw [h.zpowers_card]; exact hle)).symm

theorem orderOf_conj_eq (y c : X) : orderOf (y * c * y⁻¹) = orderOf c :=
  orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective c

theorem Core.overgroup [Finite X] (h : Core ℓ C c t)
    (hB : ∀ S : Subgroup X, S ≠ ⊥ → IsPGroup 2 S →
      ¬ ℓ ∣ Nat.card (Subgroup.normalizer (S : Set X)))
    (hD : ∀ H : Subgroup X, H ≠ ⊤ → Group.IsSolvable H) (hℓ2 : ¬ ℓ ^ 2 ∣ Nat.card X)
    {H : Subgroup X} (hCH : C ≤ H) (hH : H ≠ ⊤) :
    H ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup X) : Set X) := by
  have hcH : c ∈ H := hCH h.mem_c
  have htH : t ∈ H := hCH h.mem_t
  have := hD H hH
  have hHbot : H ≠ ⊥ := fun hb => h.c_ne_one (by simpa [hb] using hcH)
  obtain ⟨r, hr, N, hNH, hNbot, hNp, hNH'⟩ := exists_normal_pgroup_of_solvable hHbot
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hB N hNbot hNp
    have hHN : H ≤ Subgroup.normalizer (N : Set X) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hNH' y hy x hx, fun hx => ?_⟩
      have := hNH' y⁻¹ (Subgroup.inv_mem _ hy) _ hx
      simpa [mul_assoc] using this
    rw [← h.ord_c]
    exact Subgroup.orderOf_dvd_natCard _ (hHN hcH)
  have hodd : Odd (Nat.card N) := by
    have := Fact.mk hr
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow
  have hNZ : N ≤ Core.Z c :=
    h.le_Z_of_odd_normal hodd (fun w hw => hNH' t htH w hw) (fun w hw => hNH' c hcH w hw)
  obtain ⟨n, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := N)).mp hNbot
  have hHZ : ∀ y ∈ H, ∀ z ∈ Core.Z c, y * z * y⁻¹ ∈ Core.Z c := by
    intro y hy z hz
    have hn' : y * (n : X) * y⁻¹ ∈ N := hNH' y hy n n.2
    have hn1' : y * (n : X) * y⁻¹ ≠ 1 := by
      intro h1
      apply hn1
      apply Subtype.ext
      simpa using h1
    refine Core.mem_Z.mpr (h.commute_c_of_commute (hNZ hn') hn1' ?_)
    have hzn : z * (n : X) = (n : X) * z := h.comm_Z hz (hNZ n.2)
    calc y * z * y⁻¹ * (y * (n : X) * y⁻¹) = y * (z * (n : X)) * y⁻¹ := by group
      _ = y * ((n : X) * z) * y⁻¹ := by rw [hzn]
      _ = y * (n : X) * y⁻¹ * (y * z * y⁻¹) := by group
  refine le_normalizer_of_conj fun y hy => ?_
  have hdZ : y * c * y⁻¹ ∈ Core.Z c := hHZ y hy c (Core.mem_Z.mpr rfl)
  have := Fact.mk h.odd.prime
  have hdp : IsPGroup ℓ (Subgroup.zpowers (y * c * y⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_conj_eq, h.ord_c, pow_one])
  have hdnorm : y * c * y⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup X) : Set X) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => (Core.commute_zpowers hdZ hx).symm)
  have hsup := IsPGroup.to_sup_of_normal_left' h.zpowers_isPGroup hdp
    (Subgroup.zpowers_le.mpr hdnorm)
  have heq := h.sylow_max hℓ2 hsup le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

end OddFrame

end CFSG.SignalizerFunctorTheorem.McBride
