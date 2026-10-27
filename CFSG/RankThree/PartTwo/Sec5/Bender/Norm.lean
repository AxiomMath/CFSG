module

import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec5.Bender

open CFSG
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem frobenius_norm_trivial {V : Type*} [CommGroup V] {p : ℕ}
    (hp0 : 0 < p) (hV : ∀ v : V, v ^ p = 1) (T : Subgroup (MulAut V)) [Fintype T]
    (hT : Nat.Coprime p (Nat.card T))
    (β : MulAut V) (hβT : β ∈ Subgroup.normalizer (T : Set (MulAut V)))
    (hfpf : ∀ t ∈ T, ∀ i : ℕ, 0 < i → i < p → t * β ^ i = β ^ i * t → t = 1)
    (hNT : ∀ v : V, ∏ t : T, (t : MulAut V) v = 1)
    (hNβ : ∀ v : V, ∏ i ∈ Finset.range p, (β ^ i) v = 1) (v : V) : v = 1 := by
  classical
  have hconj : ∀ w : T, ∏ i ∈ Finset.range p,
      ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v = 1 := by
    intro w
    have h1 := hNβ ((w : MulAut V)⁻¹ v)
    calc ∏ i ∈ Finset.range p, ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v
        = (w : MulAut V) (∏ i ∈ Finset.range p, (β ^ i) ((w : MulAut V)⁻¹ v)) := by
          rw [map_prod]
          rfl
      _ = 1 := by rw [h1, map_one]
  have htot : ∏ i ∈ Finset.range p, ∏ w : T,
      ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v = 1 := by
    rw [Finset.prod_comm]
    exact Finset.prod_eq_one fun w _ => hconj w
  have hterm : ∀ i ∈ Finset.range p, i ≠ 0 →
      ∏ w : T, ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v = 1 := by
    intro i hi hi0
    have hip : i < p := Finset.mem_range.mp hi
    have hmem : ∀ w : T, (w : MulAut V) * β ^ i * (w : MulAut V)⁻¹ * (β ^ i)⁻¹ ∈ T := by
      intro w
      have hβi : β ^ i ∈ Subgroup.normalizer (T : Set (MulAut V)) := Subgroup.pow_mem _ hβT i
      have h2 : β ^ i * (w : MulAut V)⁻¹ * (β ^ i)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp hβi _).mp (T.inv_mem w.2)
      have h3 := T.mul_mem w.2 h2
      simpa [mul_assoc] using h3
    let σ : T → T := fun w => ⟨_, hmem w⟩
    have hσ : Function.Injective σ := by
      intro w w' hww'
      have h1 : (w : MulAut V) * β ^ i * (w : MulAut V)⁻¹ =
          (w' : MulAut V) * β ^ i * (w' : MulAut V)⁻¹ := by
        have h0 := congrArg Subtype.val hww'
        simp only [σ] at h0
        exact mul_right_cancel h0
      have h2 : ((w' : MulAut V)⁻¹ * w) * β ^ i = β ^ i * ((w' : MulAut V)⁻¹ * w) := by
        calc ((w' : MulAut V)⁻¹ * w) * β ^ i
            = (w' : MulAut V)⁻¹ * ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) * w := by group
          _ = (w' : MulAut V)⁻¹ * ((w' : MulAut V) * β ^ i * (w' : MulAut V)⁻¹) * w := by
              rw [h1]
          _ = β ^ i * ((w' : MulAut V)⁻¹ * w) := by group
      have h3 := hfpf _ (T.mul_mem (T.inv_mem w'.2) w.2) i (Nat.pos_of_ne_zero hi0) hip h2
      apply Subtype.ext
      have : (w : MulAut V) = w' := by
        have := congrArg ((w' : MulAut V) * ·) h3
        simpa using this
      exact this
    have hσb : Function.Bijective σ := Finite.injective_iff_bijective.mp hσ
    calc ∏ w : T, ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v
        = ∏ w : T, ((σ w : T) : MulAut V) ((β ^ i) v) := by
          refine Finset.prod_congr rfl fun w _ => ?_
          show ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹) v =
            ((w : MulAut V) * β ^ i * (w : MulAut V)⁻¹ * (β ^ i)⁻¹) ((β ^ i) v)
          simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
      _ = ∏ t : T, (t : MulAut V) ((β ^ i) v) :=
          Fintype.prod_bijective σ hσb _ _ fun _ => rfl
      _ = 1 := hNT _
  rw [Finset.prod_eq_single 0 (fun i hi hi0 => hterm i hi hi0)
    (fun h => absurd (Finset.mem_range.mpr hp0) h)] at htot
  simp only [pow_zero, mul_one, mul_inv_cancel, MulAut.one_apply, Finset.prod_const,
    Finset.card_univ] at htot
  have h1 := (pow_gcd_eq_one (a := v) (m := Fintype.card T) (n := p)).mpr ⟨htot, hV v⟩
  rw [Nat.gcd_comm, ← Nat.card_eq_fintype_card, Nat.Coprime.gcd_eq_one hT, pow_one] at h1
  exact h1



theorem exists_mul_mem_centralizer [Finite X] {p : ℕ} [Fact p.Prime] {K : Subgroup X}
    (hK : ¬ p ∣ Nat.card K) {b s : X} (hb : b ^ p = 1)
    (hbK : b ∈ Subgroup.normalizer (K : Set X)) (hsb : s⁻¹ * b * s * b⁻¹ ∈ K) :
    ∃ k ∈ K, s * k ∈ Subgroup.centralizer ({b} : Set X) := by
  classical
  let L : Subgroup X :=
    { carrier := {g | g ∈ Subgroup.normalizer (K : Set X) ∧ s⁻¹ * g * s * g⁻¹ ∈ K}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro g h ⟨hg, hgK⟩ ⟨hh, hhK⟩
        refine ⟨Subgroup.mul_mem _ hg hh, ?_⟩
        have h1 : g * (s⁻¹ * h * s * h⁻¹) * g⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hg _).mp hhK
        have h2 := K.mul_mem hgK h1
        have h3 : s⁻¹ * g * s * g⁻¹ * (g * (s⁻¹ * h * s * h⁻¹) * g⁻¹) =
            s⁻¹ * (g * h) * s * (g * h)⁻¹ := by group
        rwa [h3] at h2
      inv_mem' := by
        rintro g ⟨hg, hgK⟩
        refine ⟨Subgroup.inv_mem _ hg, ?_⟩
        have h1 : g⁻¹ * (s⁻¹ * g * s * g⁻¹)⁻¹ * g⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp (K.inv_mem hgK)
        have h3 : g⁻¹ * (s⁻¹ * g * s * g⁻¹)⁻¹ * g⁻¹⁻¹ = s⁻¹ * g⁻¹ * s * g⁻¹⁻¹ := by group
        rwa [h3] at h1 }
  have hbL : b ∈ L := ⟨hbK, hsb⟩
  have hBL : Subgroup.zpowers b ≤ L := Subgroup.zpowers_le.mpr hbL
  have hB : IsPGroup p (Subgroup.zpowers b) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  let act : MulAction (Subgroup.zpowers b) K :=
    { smul := fun g k => ⟨s⁻¹ * (g : X) * s * (k : X) * (g : X)⁻¹, by
        have h1 := (hBL g.2).2
        have h2 := (Subgroup.mem_normalizer_iff.mp (hBL g.2).1 k).mp k.2
        have h3 : s⁻¹ * (g : X) * s * (k : X) * (g : X)⁻¹ =
            (s⁻¹ * g * s * (g : X)⁻¹) * (g * k * (g : X)⁻¹) := by group
        rw [h3]
        exact K.mul_mem h1 h2⟩
      one_smul := fun k => by
        apply Subtype.ext
        change s⁻¹ * ((1 : Subgroup.zpowers b) : X) * s * (k : X) *
          ((1 : Subgroup.zpowers b) : X)⁻¹ = k
        simp
      mul_smul := fun g h k => by
        apply Subtype.ext
        change s⁻¹ * ((g * h : Subgroup.zpowers b) : X) * s * (k : X) *
          ((g * h : Subgroup.zpowers b) : X)⁻¹ =
          s⁻¹ * (g : X) * s * (s⁻¹ * (h : X) * s * (k : X) * (h : X)⁻¹) * (g : X)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  obtain ⟨k, hk⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card K hK
  refine ⟨k, k.2, ?_⟩
  have h1 : s⁻¹ * b * s * (k : X) * b⁻¹ = k :=
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hk ⟨b, Subgroup.mem_zpowers b⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : b * (s * k) * b⁻¹ = s * k := by
    calc b * (s * k) * b⁻¹ = s * (s⁻¹ * b * s * (k : X) * b⁻¹) := by group
      _ = s * k := by rw [h1]
  calc s * k * b = b * (s * k) * b⁻¹ * b := by rw [h2]
    _ = b * (s * k) := by group





@[expose] def conjOf (Z : Subgroup X) (g : X) (hg : g ∈ Subgroup.normalizer (Z : Set X)) :
    Z →* Z where
  toFun z := ⟨g * z * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg z).mp z.2⟩
  map_one' := by ext; simp
  map_mul' y z := by ext; simp only [Subgroup.coe_mul]; group

theorem coe_conjOf (Z : Subgroup X) (g : X) (hg : g ∈ Subgroup.normalizer (Z : Set X)) (z : Z) :
    ((conjOf Z g hg z : Z) : X) = g * z * g⁻¹ := rfl

theorem norm_trick {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {P : Subgroup X}
    (hcl : ⁅P, P⁆ ≤ Subgroup.centralizer (P : Set X)) {a : X}
    (ha : a ∈ Subgroup.normalizer (P : Set X)) (hap : a ^ p = 1) {x : X} (hx : x ∈ P) :
    (x * a) ^ p ∈ P ∧ ∃ z ∈ ⁅P, P⁆, (x * a) ^ p * z ∈ Subgroup.centralizer ({a} : Set X) := by
  classical
  set Z := ⁅P, P⁆ with hZdef
  have hZP : Z ≤ P := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg)) (P.inv_mem hh)
  have hcomm : ∀ y ∈ Z, ∀ u ∈ P, y * u = u * y := fun y hy u hu =>
    (Subgroup.mem_centralizer_iff.mp (hcl hy) u hu).symm
  let _ : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun y z => Subtype.ext (hcomm y y.2 z (hZP z.2)) }
  have haZ : a ∈ Subgroup.normalizer (Z : Set X) :=
    CFSG.RankThree.PartTwo.Source.mem_normalizer_commutator ha ha
  have hapZ : ∀ j : ℕ, a ^ j ∈ Subgroup.normalizer (Z : Set X) := fun j =>
    Subgroup.pow_mem _ haZ j
  set xs : ℕ → X := fun i => a ^ i * x * (a ^ i)⁻¹ with hxs
  have hxsP : ∀ i, xs i ∈ P := fun i =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ha i) x).mp hx
  set m : ℕ → X := fun k => ((List.range k).map xs).prod with hm
  have hmsucc : ∀ k, m (k + 1) = m k * xs k := by
    intro k
    simp only [m, List.range_succ, List.map_append, List.prod_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hmP : ∀ k, m k ∈ P := by
    intro k
    induction k with
    | zero => simp [m, P.one_mem]
    | succ k ih => rw [hmsucc]; exact P.mul_mem ih (hxsP k)
  have hpow : ∀ k, (x * a) ^ k = m k * a ^ k := by
    intro k
    induction k with
    | zero => simp [m]
    | succ k ih =>
      rw [pow_succ, ih, hmsucc]
      simp only [xs]
      group
  have hn : (x * a) ^ p = m p := by rw [hpow, hap, mul_one]
  set n := (x * a) ^ p with hndef
  have hnP : n ∈ P := hn ▸ hmP p
  refine ⟨hnP, ?_⟩
  have hconj : a * n * a⁻¹ = x⁻¹ * n * x := by
    have h1 : a * n * a⁻¹ = (a * (x * a) * a⁻¹) ^ p := by rw [conj_pow]
    have h2 : a * (x * a) * a⁻¹ = x⁻¹ * (x * a) * x⁻¹⁻¹ := by group
    rw [h1, h2, conj_pow, inv_inv]
  have hccZ : ∀ u ∈ P, ∀ w ∈ P, u⁻¹ * w⁻¹ * u * w ∈ Z := by
    intro u hu w hw
    have := Subgroup.commutator_mem_commutator (P.inv_mem hu) (P.inv_mem hw)
    rw [commutatorElement_def, inv_inv, inv_inv] at this
    exact this
  have hbil : ∀ u ∈ P, ∀ v ∈ P, ∀ w ∈ P,
      (u * v)⁻¹ * w⁻¹ * (u * v) * w = (u⁻¹ * w⁻¹ * u * w) * (v⁻¹ * w⁻¹ * v * w) := by
    intro u hu v hv w hw
    have hc := hcomm _ (hccZ u hu w hw) v⁻¹ (P.inv_mem hv)
    calc (u * v)⁻¹ * w⁻¹ * (u * v) * w = v⁻¹ * (u⁻¹ * w⁻¹ * u * w) * w⁻¹ * v * w := by group
      _ = (u⁻¹ * w⁻¹ * u * w) * v⁻¹ * w⁻¹ * v * w := by rw [← hc]
      _ = (u⁻¹ * w⁻¹ * u * w) * (v⁻¹ * w⁻¹ * v * w) := by group
  let cZ : ℕ → Z := fun i => ⟨(xs i)⁻¹ * x⁻¹ * xs i * x, hccZ _ (hxsP i) _ hx⟩
  have hprod : ∀ k, ((∏ i ∈ Finset.range k, cZ i : Z) : X) = (m k)⁻¹ * x⁻¹ * m k * x := by
    intro k
    induction k with
    | zero => simp [m]
    | succ k ih =>
      rw [Finset.prod_range_succ, Subgroup.coe_mul, ih, hmsucc,
        hbil _ (hmP k) _ (hxsP k) _ hx]
  set δ : Z →* Z := MonoidHom.id Z / conjOf Z a haZ with hδ
  have hδapply : ∀ z : Z, ((δ z : Z) : X) = z * (a * z * a⁻¹)⁻¹ := by
    intro z
    simp [δ, div_eq_mul_inv, coe_conjOf]
  have hL : ∀ (j : ℕ) (z : Z), z * (conjOf Z (a ^ j) (hapZ j) z)⁻¹ ∈ δ.range := by
    intro j z
    induction j with
    | zero =>
      have : conjOf Z (a ^ 0) (hapZ 0) z = z := by ext; simp [coe_conjOf]
      rw [this, mul_inv_cancel]
      exact Subgroup.one_mem _
    | succ j ih =>
      have h1 : z * (conjOf Z (a ^ (j + 1)) (hapZ (j + 1)) z)⁻¹ =
          (z * (conjOf Z (a ^ j) (hapZ j) z)⁻¹) * δ (conjOf Z (a ^ j) (hapZ j) z) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hδapply, coe_conjOf, pow_succ']
        group
      rw [h1]
      exact Subgroup.mul_mem _ ih ⟨_, rfl⟩
  have hpair : ∀ i, 0 < i → i < p →
      cZ (p - i) = (conjOf Z (a ^ (p - i)) (hapZ (p - i)) (cZ i))⁻¹ := by
    intro i hi0 hip
    apply Subtype.ext
    have hxsp : a ^ (p - i) * xs i * (a ^ (p - i))⁻¹ = x := by
      simp only [xs]
      have : a ^ (p - i) * (a ^ i * x * (a ^ i)⁻¹) * (a ^ (p - i))⁻¹ =
          a ^ (p - i + i) * x * (a ^ (p - i + i))⁻¹ := by rw [pow_add]; group
      rw [this, Nat.sub_add_cancel hip.le, hap, one_mul, inv_one, mul_one]
    simp only [cZ, Subgroup.coe_inv, coe_conjOf]
    have hj : xs (p - i) = a ^ (p - i) * x * (a ^ (p - i))⁻¹ := rfl
    rw [hj]
    calc (a ^ (p - i) * x * (a ^ (p - i))⁻¹)⁻¹ * x⁻¹ * (a ^ (p - i) * x * (a ^ (p - i))⁻¹) * x
        = (a ^ (p - i) * x * (a ^ (p - i))⁻¹)⁻¹ *
            (a ^ (p - i) * xs i * (a ^ (p - i))⁻¹)⁻¹ * (a ^ (p - i) * x * (a ^ (p - i))⁻¹) *
            (a ^ (p - i) * xs i * (a ^ (p - i))⁻¹) := by rw [hxsp]
      _ = (a ^ (p - i) * ((xs i)⁻¹ * x⁻¹ * xs i * x) * (a ^ (p - i))⁻¹)⁻¹ := by group
  have hc0 : cZ 0 = 1 := by
    apply Subtype.ext
    simp [cZ, xs]
  have hmem : (∏ i ∈ Finset.range p, cZ i) ∈ δ.range := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_prod]
    refine Finset.prod_involution (fun i _ => if i = 0 then 0 else p - i) ?_ ?_ ?_ ?_
    · intro i hi
      by_cases h0 : i = 0
      · rw [ite_eq_left h0, h0, hc0, map_one, mul_one]
      · rw [ite_eq_right h0, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          hpair i (Nat.pos_of_ne_zero h0) (Finset.mem_range.mp hi)]
        exact hL _ _
    · intro i hi hne
      by_cases h0 : i = 0
      · exfalso
        apply hne
        simp [h0, hc0]
      · rw [ite_eq_right h0]
        intro h
        have hip := Finset.mem_range.mp hi
        have hodd : Odd p := hp.odd_of_ne_two hp2
        obtain ⟨k, hk⟩ := hodd
        omega
    · intro i hi
      by_cases h0 : i = 0
      · rw [ite_eq_left h0]
        exact Finset.mem_range.mpr hp.pos
      · rw [ite_eq_right h0]
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)
    · intro i hi
      by_cases h0 : i = 0
      · simp [h0]
      · have hip := Finset.mem_range.mp hi
        have h1 : p - i ≠ 0 := by omega
        rw [ite_eq_right h0, ite_eq_right h1]
        omega
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, w.2, ?_⟩
  have hd : (w : X) * (a * w * a⁻¹)⁻¹ = n⁻¹ * x⁻¹ * n * x := by
    rw [← hδapply, hw, hprod, ← hn]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have key : a * (n * w) * a⁻¹ = n * w := by
    calc a * (n * w) * a⁻¹ = (a * n * a⁻¹) * (a * w * a⁻¹) := by group
      _ = (x⁻¹ * n * x) * (a * w * a⁻¹) := by rw [hconj]
      _ = n * ((n⁻¹ * x⁻¹ * n * x) * (a * w * a⁻¹)) := by group
      _ = n * w := by rw [← hd]; group
  calc n * w * a = a * (n * w) * a⁻¹ * a := by rw [key]
    _ = a * (n * w) := by group





theorem commute_of_commute_pow {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) {g t : M}
    (hg : g ^ p = 1) {i : ℕ} (hi0 : 0 < i) (hip : i < p) (h : t * g ^ i = g ^ i * t) :
    t * g = g * t := by
  have hcop : Nat.Coprime i p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact absurd (Nat.le_of_dvd hi0 hd) (by omega)
  have hgcd := Nat.gcd_eq_gcd_ab i p
  rw [hcop.gcd_eq_one, Nat.cast_one] at hgcd
  have hgeq : g = (g ^ i) ^ (Nat.gcdA i p) := by
    calc g = g ^ (1 : ℤ) := (zpow_one g).symm
      _ = g ^ ((i : ℤ) * Nat.gcdA i p + (p : ℤ) * Nat.gcdB i p) := by rw [← hgcd]
      _ = (g ^ i) ^ (Nat.gcdA i p) * (g ^ p) ^ (Nat.gcdB i p) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (g ^ i) ^ (Nat.gcdA i p) := by rw [hg, one_zpow, mul_one]
  have hc : Commute t (g ^ i) := h
  rw [hgeq]
  exact (hc.zpow_right _).eq

end CFSG.RankThree.PartTwo.Sec5.Bender
