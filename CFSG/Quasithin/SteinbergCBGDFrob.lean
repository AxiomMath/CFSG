module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Polynomial

variable {K : Type*} [Field K]

@[expose] def fixF (σ : K ≃+* K) (n : ℕ) : Subfield K :=
  RingHom.eqLocusField ((σ ^ n : K ≃+* K) : K →+* K) (RingHom.id K)

theorem mem_fixF {σ : K ≃+* K} {n : ℕ} {x : K} : x ∈ fixF σ n ↔ (σ ^ n) x = x :=
  RingHom.mem_eqLocusField

variable {σ : K ≃+* K}

theorem zpow_apply_of_apply {τ : K ≃+* K} {x : K} (hx : τ x = x) (k : ℤ) : (τ ^ k) x = x := by
  have hstab : Subgroup.zpowers τ ≤ MulAction.stabilizer (K ≃+* K) x :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx
  exact hstab (Subgroup.zpow_mem_zpowers τ k)

theorem fixF_le_of_dvd {a b : ℕ} (hab : a ∣ b) : fixF σ a ≤ fixF σ b := by
  obtain ⟨c, rfl⟩ := hab
  intro x hx
  rw [mem_fixF] at hx ⊢
  rw [pow_mul]
  rw [show ((σ ^ a) ^ c : K ≃+* K) = (σ ^ a) ^ (c : ℤ) by rw [zpow_natCast]]
  exact zpow_apply_of_apply hx c

theorem exists_fixF_of_finset (hK : ∀ x : K, ∃ n, 1 ≤ n ∧ x ∈ fixF σ n) (S : Finset K) :
    ∃ n, 1 ≤ n ∧ ∀ x ∈ S, x ∈ fixF σ n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, by simp⟩
  | insert a S _ ih =>
    obtain ⟨n, hn, hS⟩ := ih
    obtain ⟨m, hm, ha⟩ := hK a
    refine ⟨m * n, Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact fixF_le_of_dvd (dvd_mul_right m n) ha
    · exact fixF_le_of_dvd (dvd_mul_left n m) (hS x hx)

variable {p : ℕ}

theorem pow_apply_eq (hσ : ∀ x, σ x = x ^ p) (n : ℕ) (x : K) : (σ ^ n) x = x ^ p ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, hσ, ih, ← pow_mul, pow_succ, mul_comm]

theorem mem_fixF_iff (hσ : ∀ x, σ x = x ^ p) {n : ℕ} {x : K} :
    x ∈ fixF σ n ↔ x ^ p ^ n = x := by
  rw [mem_fixF, pow_apply_eq hσ]

variable [hp : Fact p.Prime] [CharP K p]

theorem card_fixF [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (fixF σ n) = p ^ n := by
  classical
  set f : K[X] := X ^ p ^ n - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K (by omega) hp.out.one_lt
  have hsep : f.Separable := galois_poly_separable p (p ^ n) (dvd_pow_self p (by omega))
  have hdeg : f.natDegree = p ^ n :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K (Nat.one_lt_pow (by omega) hp.out.one_lt)
  have hcard : Multiset.card f.roots = p ^ n := by
    rw [← hdeg]
    exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits f)
  have hset : ((fixF σ n : Subfield K) : Set K) = (f.roots.toFinset : Set K) := by
    ext x
    rw [SetLike.mem_coe, mem_fixF_iff hσ, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hf0,
      IsRoot, hf, eval_sub, eval_pow, eval_X, sub_eq_zero]
  change Nat.card ((fixF σ n : Subfield K) : Set K) = p ^ n
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Multiset.toFinset_card_of_nodup (nodup_roots hsep), hcard]

theorem finite_fixF [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) {n : ℕ} (hn : 1 ≤ n) :
    Finite (fixF σ n) :=
  Nat.finite_of_card_ne_zero (by rw [card_fixF hσ hn]; exact (pow_pos hp.out.pos n).ne')

omit [CharP K p] in
theorem le_fixF_of_card (hσ : ∀ x, σ x = x ^ p) {E : Subfield K} {n : ℕ}
    (hE : Nat.card E = p ^ n) : E ≤ fixF σ n := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact (pow_pos hp.out.pos n).ne')
  have := Fintype.ofFinite E
  intro x hx
  rw [mem_fixF_iff hσ]
  have h := FiniteField.pow_card (⟨x, hx⟩ : E)
  rw [Fintype.card_eq_nat_card, hE] at h
  have h' := congrArg Subtype.val h
  rw [SubmonoidClass.coe_pow] at h'
  exact h'

theorem eq_fixF_of_card [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) {E : Subfield K} {n : ℕ}
    (hn : 1 ≤ n) (hE : Nat.card E = p ^ n) : E = fixF σ n := by
  have hle := le_fixF_of_card hσ hE
  have := finite_fixF hσ hn
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card (fixF σ n) ≤ Nat.card E
  rw [card_fixF hσ hn, hE]

theorem exists_eq_fixF [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) (E : Subfield K) [Finite E] :
    ∃ n, 1 ≤ n ∧ Nat.card E = p ^ n ∧ E = fixF σ n := by
  have := Fintype.ofFinite E
  obtain ⟨n, -, hcard⟩ := FiniteField.card E p
  have hcard' : Nat.card E = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  exact ⟨n, n.pos, hcard', eq_fixF_of_card hσ n.pos hcard'⟩

theorem zpow_fix_iff [IsAlgClosed K] (hσ : ∀ x, σ x = x ^ p) {e : ℕ} (he : 1 ≤ e) (i : ℤ) :
    (∀ x ∈ fixF σ e, (σ ^ i) x = x) ↔ (e : ℤ) ∣ i := by
  have hmul : ∀ k : ℤ, ∀ x ∈ fixF σ e, (σ ^ ((e : ℤ) * k)) x = x := by
    intro k x hx
    rw [zpow_mul, zpow_natCast]
    exact zpow_apply_of_apply (mem_fixF.1 hx) k
  constructor
  · intro h
    set s := i % (e : ℤ) with hs
    have hs0 : 0 ≤ s := Int.emod_nonneg i (by omega)
    have hse : s < e := Int.emod_lt_of_pos i (by omega)
    have hfix : ∀ x ∈ fixF σ e, (σ ^ s) x = x := by
      intro x hx
      have hsi : s = i + (e : ℤ) * (-(i / (e : ℤ))) := by
        rw [hs, Int.emod_def]
        ring
      rw [hsi, zpow_add, RingAut.mul_apply, hmul _ x hx, h x hx]
    by_contra hdvd
    have hs1 : 1 ≤ s.toNat := by
      have : s ≠ 0 := fun h0 => hdvd (Int.dvd_of_emod_eq_zero h0)
      omega
    have hle : fixF σ e ≤ fixF σ s.toNat := by
      intro x hx
      rw [mem_fixF, ← zpow_natCast, Int.toNat_of_nonneg hs0]
      exact hfix x hx
    have := finite_fixF hσ hs1
    have hc := Nat.card_mono (Set.toFinite ((fixF σ s.toNat : Subfield K) : Set K)) hle
    change Nat.card (fixF σ e) ≤ Nat.card (fixF σ s.toNat) at hc
    rw [card_fixF hσ he, card_fixF hσ hs1] at hc
    have hlt : s.toNat < e := by omega
    exact absurd (Nat.pow_lt_pow_right hp.out.one_lt hlt) (not_lt.2 hc)
  · rintro ⟨k, rfl⟩ x hx
    exact hmul k x hx

end CFSG.Quasithin.SteinbergCB.GDescent
