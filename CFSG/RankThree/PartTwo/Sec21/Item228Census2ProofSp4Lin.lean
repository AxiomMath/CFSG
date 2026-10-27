module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof

open Module Polynomial

theorem not_five_dvd_pow_sub_one {q j : ℕ} (hq : q % 5 = 2 ∨ q % 5 = 3) (hj1 : 1 ≤ j)
    (hj3 : j ≤ 3) : ¬ 5 ∣ q ^ j - 1 := by
  have h : q ^ j % 5 = (q % 5) ^ j % 5 := Nat.pow_mod q j 5
  have hpos : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  generalize q ^ j = Q at h hpos
  interval_cases j <;> rcases hq with hq | hq <;> rw [hq] at h <;> norm_num at h <;> omega

theorem not_five_dvd_prod_GL {q d : ℕ} (hq : q % 5 = 2 ∨ q % 5 = 3) (hd : d ≤ 3) :
    ¬ 5 ∣ ∏ i : Fin d, (q ^ d - q ^ (i : ℕ)) := by
  rw [Prime.dvd_finsetProd_iff Nat.prime_five.prime]
  rintro ⟨i, -, hi⟩
  have hq0 : ¬ 5 ∣ q := by omega
  have hsplit : q ^ d - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (d - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [hsplit] at hi
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hi with h | h
  · exact hq0 (Nat.prime_five.dvd_of_dvd_pow h)
  · exact not_five_dvd_pow_sub_one hq (by have := i.2; omega) (by omega) h

variable {K : Type*} [Field K] [Fintype K]

theorem eq_one_of_pow_five_eq_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3)
    (hV : finrank K V ≤ 3) {c : Module.End K V} (hc : c ^ 5 = 1) : c = 1 := by
  let u : (Module.End K V)ˣ := ⟨c, c ^ 4, by rw [← pow_succ']; exact hc,
    by rw [← pow_succ]; exact hc⟩
  have hu5 : u ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hc)
  let f := Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toMulEquiv
  have h1 : orderOf u ∣ 5 := orderOf_dvd_of_pow_eq_one hu5
  have h2 : orderOf u ∣ Nat.card (GL (Fin (finrank K V)) K) := by
    rw [← orderOf_injective f.toMonoidHom f.injective]
    exact orderOf_dvd_natCard _
  rw [Matrix.card_GL_field] at h2
  have h3 : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) (not_five_dvd_prod_GL hq hV)
  exact congrArg Units.val (orderOf_eq_one_iff.mp h3)

theorem apply_eq_of_invariant {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) {c : Module.End K V} (hc : c ^ 5 = 1)
    {U : Submodule K V} (hU : ∀ x ∈ U, c x ∈ U) (hdim : finrank K U ≤ 3) {x : V} (hx : x ∈ U) :
    c x = x := by
  have h5 : (c.restrict hU) ^ 5 = 1 := by
    rw [Module.End.pow_restrict]
    ext y
    simp [LinearMap.restrict_apply, hc]
  have h1 := eq_one_of_pow_five_eq_one hq hdim h5
  have := congrArg Subtype.val (LinearMap.congr_fun h1 ⟨x, hx⟩)
  simpa using this

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {N : R} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : R) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have : (k : R) * N * N = 0 := by rw [mul_assoc, hN, mul_zero]
    push_cast
    rw [add_mul, one_mul, mul_add, mul_one, this, add_zero, add_mul, one_mul]
    abel

theorem five_ne_zero_of_card_mod (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) :
    (5 : K) ≠ 0 := by
  intro h5
  have hc := FiniteField.cast_card_eq_zero K
  rw [← Nat.div_add_mod (Fintype.card K) 5] at hc
  push_cast at hc
  rw [h5, zero_mul, zero_add] at hc
  rcases hq with hq | hq <;> rw [hq] at hc <;> push_cast at hc
  · exact one_ne_zero (by linear_combination h5 - 2 * hc : (1 : K) = 0)
  · exact one_ne_zero (by linear_combination 2 * hc - h5 : (1 : K) = 0)

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem ker_sub_one_eq_bot (hV : finrank K V = 4)
    (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) {c : Module.End K V}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) : LinearMap.ker (c - 1) = ⊥ := by
  by_cases hR : LinearMap.range (c - 1) = ⊤
  · exact LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr
      (LinearMap.range_eq_top.mp hR))
  · exfalso
    have hinv : ∀ x ∈ LinearMap.range (c - 1), c x ∈ LinearMap.range (c - 1) := by
      rintro _ ⟨y, rfl⟩
      refine ⟨c y, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have hdim : finrank K (LinearMap.range (c - 1)) ≤ 3 := by
      have := Submodule.finrank_lt hR
      omega
    have hNN : (c - 1) * (c - 1) = 0 := by
      ext y
      have h := apply_eq_of_invariant hq hc5 hinv hdim (LinearMap.mem_range_self (c - 1) y)
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      rw [LinearMap.sub_apply (c) 1 ((c - 1) y), Module.End.one_apply, h, sub_self]
    have hpow := one_add_pow_of_mul_self_eq_zero hNN 5
    rw [add_sub_cancel, hc5] at hpow
    have h5N : (5 : Module.End K V) * (c - 1) = 0 := by
      have := congrArg (· - 1) hpow
      simp only [sub_self, add_sub_cancel_left] at this
      exact_mod_cast this.symm
    apply hc1
    rw [← sub_eq_zero]
    have h5 := five_ne_zero_of_card_mod hq
    ext y
    have := LinearMap.congr_fun h5N y
    rw [Module.End.mul_apply, LinearMap.zero_apply] at this
    have h5' : (5 : Module.End K V) ((c - 1) y) = (5 : K) • (c - 1) y := by
      rw [show (5 : Module.End K V) = (5 : K) • (1 : Module.End K V) by
        rw [← Nat.cast_ofNat, ← Nat.cast_ofNat (R := K), Nat.cast_smul_eq_nsmul, nsmul_eq_mul,
          mul_one]]
      rfl
    rw [h5'] at this
    rw [LinearMap.zero_apply]
    exact (smul_eq_zero.mp this).resolve_left h5

theorem eq_bot_of_invariant (hV : finrank K V = 4)
    (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) {c : Module.End K V}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) {U : Submodule K V} (hU : ∀ x ∈ U, c x ∈ U)
    (hne : U ≠ ⊤) : U = ⊥ := by
  have hdim : finrank K U ≤ 3 := by
    have := Submodule.finrank_lt hne
    omega
  rw [eq_bot_iff]
  intro x hx
  have h := apply_eq_of_invariant hq hc5 hU hdim hx
  have hk : x ∈ LinearMap.ker (c - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
  rwa [ker_sub_one_eq_bot hV hq hc5 hc1] at hk

omit [Fintype K] [FiniteDimensional K V] in
theorem commute_aeval {a c : Module.End K V} (hac : a * c = c * a) (p : K[X]) :
    a * aeval c p = aeval c p * a := by
  have h : Commute a c := hac
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (h.pow_right i).eq]

theorem exists_polynomial_eq (hV : finrank K V = 4)
    (hq : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) {a c : Module.End K V}
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) (hac : a * c = c * a) : ∃ p : K[X], a = aeval c p := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set U := Submodule.span K (Set.range fun i : Fin 5 => (c ^ (i : ℕ)) v) with hUdef
  have hUinv : ∀ x ∈ U, c x ∈ U := by
    intro x hx
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [← Module.End.mul_apply, ← pow_succ']
    by_cases hi : (i : ℕ) = 4
    · rw [hi, hc5, Module.End.one_apply]
      exact Submodule.subset_span ⟨0, by simp⟩
    · exact Submodule.subset_span ⟨⟨i + 1, by omega⟩, rfl⟩
  have hvU : v ∈ U := Submodule.subset_span ⟨0, by simp⟩
  have hUtop : U = ⊤ := by
    by_contra hne
    have := eq_bot_of_invariant hV hq hc5 hc1 hUinv hne
    rw [this, Submodule.mem_bot] at hvU
    exact hv hvU
  have hspan : ∀ w : V, ∃ r : K[X], w = aeval c r v := by
    intro w
    have hw : w ∈ U := hUtop ▸ Submodule.mem_top
    obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
    refine ⟨∑ i : Fin 5, Polynomial.C (s i) * X ^ (i : ℕ), ?_⟩
    simp [map_sum, LinearMap.sum_apply, Polynomial.aeval_C]
  obtain ⟨p, hp⟩ := hspan (a v)
  refine ⟨p, LinearMap.ext fun w => ?_⟩
  obtain ⟨r, rfl⟩ := hspan w
  rw [← Module.End.mul_apply, commute_aeval hac r, Module.End.mul_apply, hp,
    ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

omit [Fintype K] [FiniteDimensional K V] in
theorem bilin_pow_pow (B : LinearMap.BilinForm K V) {c : Module.End K V}
    (hc : ∀ x y, B (c x) (c y) = B x y) (i : ℕ) (x y : V) :
    B ((c ^ i) x) ((c ^ i) y) = B x y := by
  induction i generalizing x y with
  | zero => simp
  | succ i ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hc]

omit [Fintype K] [FiniteDimensional K V] in
theorem bilin_aeval_left (B : LinearMap.BilinForm K V) {c : Module.End K V}
    (hc : ∀ x y, B (c x) (c y) = B x y) (hc5 : c ^ 5 = 1) (p : K[X]) (x y : V) :
    B (aeval c p x) y = B x (aeval (c ^ 4) p y) := by
  have hmono : ∀ i : ℕ, B ((c ^ i) x) y = B x (((c ^ 4) ^ i) y) := by
    intro i
    have h1 : (c ^ i) (((c ^ 4) ^ i) y) = y := by
      rw [← Module.End.mul_apply, ← pow_mul, ← pow_add, show i + 4 * i = 5 * i by ring, pow_mul,
        hc5, one_pow, Module.End.one_apply]
    conv_lhs => rw [← h1]
    exact bilin_pow_pow B hc i x _
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, map_smul,
    hmono]

omit [FiniteDimensional K V] in
theorem aeval_pow_card_sq {c : Module.End K V} (hc5 : c ^ 5 = 1)
    (hq : Fintype.card K ^ 2 % 5 = 4) (p : K[X]) :
    (aeval c p) ^ (Fintype.card K ^ 2) = aeval (c ^ 4) p := by
  set q := Fintype.card K
  have hexp : p ^ (q ^ 2) = expand K (q ^ 2) p := by
    rw [sq, expand_mul, FiniteField.Polynomial.expand_card p, map_pow,
      FiniteField.Polynomial.expand_card p, ← pow_mul]
  have hc : c ^ (q ^ 2) = c ^ 4 := by
    rw [← Nat.div_add_mod (q ^ 2) 5, hq, pow_add, pow_mul, hc5, one_pow, one_mul]
  rw [← map_pow, hexp, expand_aeval, hc]

theorem no_commuting_isometries_three_five (hV : finrank K V = 4)
    (hq5 : Fintype.card K % 5 = 2 ∨ Fintype.card K % 5 = 3) (hq3 : Fintype.card K % 3 ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : ∀ w, (∀ v, B v w = 0) → w = 0)
    {a c : Module.End K V} (ha : ∀ x y, B (a x) (a y) = B x y)
    (hc : ∀ x y, B (c x) (c y) = B x y) (hac : a * c = c * a) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1) : False := by
  obtain ⟨p, hp⟩ := exists_polynomial_eq hV hq5 hc5 hc1 hac
  have hadj : aeval (c ^ 4) p * a = 1 := by
    ext y
    refine sub_eq_zero.mp (hB _ fun x => ?_)
    rw [map_sub, Module.End.mul_apply, Module.End.one_apply, ← bilin_aeval_left B hc hc5, ← hp,
      ha, sub_self]
  have hq2 : Fintype.card K ^ 2 % 5 = 4 := by
    rw [Nat.pow_mod]
    rcases hq5 with h | h <;> rw [h]
  have ha' : a ^ (Fintype.card K ^ 2) = a := by
    have h3 : Fintype.card K ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod]
      have : Fintype.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases h : Fintype.card K % 3 <;> simp_all
    rw [← Nat.div_add_mod (Fintype.card K ^ 2) 3, h3, pow_add, pow_mul, ha3, one_pow, one_mul,
      pow_one]
  have hfrob := aeval_pow_card_sq hc5 hq2 p
  rw [← hp, ha'] at hfrob
  rw [← hfrob] at hadj
  apply ha1
  calc a = a * (a * a) := by rw [hadj, mul_one]
    _ = a ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
    _ = 1 := ha3

end CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof
