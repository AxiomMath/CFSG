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

namespace CFSG.RankThree.PartOne.KE.CTE6

theorem eq_five_or_seven {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp7 : p ≤ 7) :
    p = 5 ∨ p = 7 := by
  interval_cases p <;> first | omega | (exfalso; revert hp; decide)

theorem natCast_ne_zero_of_lt {p c : ℕ} (hc : 0 < c) (hcp : c < p) :
    ((c : ℕ) : ZMod p) ≠ 0 :=
  fun h => absurd (Nat.le_of_dvd hc ((ZMod.natCast_eq_zero_iff c p).1 h)) (by omega)

theorem not_dvd_natCast_of_lt {p c : ℕ} (hc : 0 < c) (hcp : c < p) : ¬ (p : ℤ) ∣ (c : ℤ) :=
  fun h => Nat.not_dvd_of_pos_of_lt hc hcp (Int.natCast_dvd_natCast.1 h)

theorem not_dvd_natCast_mul {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (hcp : c < p) {y : ℤ}
    (hy : ¬ (p : ℤ) ∣ y) : ¬ (p : ℤ) ∣ (c : ℤ) * y :=
  (Nat.prime_iff_prime_int.mp hp).not_dvd_mul (not_dvd_natCast_of_lt hc hcp) hy

theorem not_dvd_of_pow_ne_one {p q d : ℕ} (hne : (q : ZMod p) ^ d ≠ 1) {P Q : ℤ}
    (h : (q : ℤ) ^ d - 1 = P * Q) : ¬ (p : ℤ) ∣ P := by
  intro hd
  apply hne
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ d - 1 := h ▸ dvd_mul_of_dvd_left hd Q
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
  push_cast at h2
  exact sub_eq_zero.1 h2

theorem pow_ne_one_of_orderOf {p q m d : ℕ} (hord : orderOf (q : ZMod p) = m) (hmd : ¬ m ∣ d) :
    (q : ZMod p) ^ d ≠ 1 :=
  fun h => hmd (hord ▸ orderOf_dvd_iff_pow_eq_one.2 h)

theorem dvd_pow_sub_one_iff {p q m d : ℕ} (hq : 1 ≤ q) (hord : orderOf (q : ZMod p) = m) :
    p ∣ q ^ d - 1 ↔ m ∣ d := by
  rw [← hord, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]
  simp

theorem ordProj_eq_one_of_not_dvd {p n : ℕ} (h : ¬ p ∣ n) : ordProj[p] n = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

theorem ordProj_eq_of_int_factor {p N n : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) {R : ℤ}
    (hfac : (N : ℤ) = n * R) (hpR : ¬ (p : ℤ) ∣ R) : ordProj[p] N = ordProj[p] n := by
  have hR0 : R ≠ 0 := by
    rintro rfl
    simp at hfac
    exact hN hfac
  have hNn : N = n * R.natAbs := by
    have := congrArg Int.natAbs hfac
    simpa [Int.natAbs_mul] using this
  have hRn : R.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hR0
  have hpR' : ¬ p ∣ R.natAbs := fun h => hpR (Int.natCast_dvd.2 h)
  rw [hNn, Nat.ordProj_mul p hn hRn, ordProj_eq_one_of_not_dvd hpR', mul_one]

theorem prod_map_ordProj_eq_single {p q m : ℕ} (hq : 1 ≤ q) (hord : orderOf (q : ZMod p) = m)
    {D : List ℕ} (hD : D.Nodup) {d₀ : ℕ} (hd₀ : d₀ ∈ D) (hrest : ∀ d ∈ D, d ≠ d₀ → ¬ m ∣ d) :
    (D.map fun d => ordProj[p] (q ^ d - 1)).prod = ordProj[p] (q ^ d₀ - 1) := by
  rw [← List.prod_map_erase _ hd₀]
  have h1 : ((D.erase d₀).map fun d => ordProj[p] (q ^ d - 1)).prod = 1 := by
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    rw [hD.mem_erase_iff] at hd
    exact ordProj_eq_one_of_not_dvd (fun h => hrest d hd.2 hd.1
      ((dvd_pow_sub_one_iff hq hord).1 h))
  rw [h1, mul_one]

theorem prime_dvd_eight {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 8) : ℓ = 2 := by
  have : ℓ ≤ 8 := Nat.le_of_dvd (by norm_num) h
  interval_cases ℓ <;> first | omega | (exfalso; revert hℓ; decide)

theorem prime_dvd_nine {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 9) : ℓ = 3 := by
  have : ℓ ≤ 9 := Nat.le_of_dvd (by norm_num) h
  interval_cases ℓ <;> first | omega | (exfalso; revert hℓ; decide)

theorem prime_dvd_twelve {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 12) : ℓ = 2 ∨ ℓ = 3 := by
  have : ℓ ≤ 12 := Nat.le_of_dvd (by norm_num) h
  interval_cases ℓ <;> first | omega | (exfalso; revert hℓ; decide)

theorem prime_dvd_eighteen {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 18) : ℓ = 2 ∨ ℓ = 3 := by
  have : ℓ ≤ 18 := Nat.le_of_dvd (by norm_num) h
  interval_cases ℓ <;> first | omega | (exfalso; revert hℓ; decide)

theorem no_root5_phi8 : ∀ y : ZMod 5, y ^ 4 + 1 ≠ 0 := by decide

theorem no_root7_phi8 : ∀ y : ZMod 7, y ^ 4 + 1 ≠ 0 := by decide

theorem no_root5_phi12 : ∀ y : ZMod 5, y ^ 4 - y ^ 2 + 1 ≠ 0 := by decide

theorem no_root7_phi12 : ∀ y : ZMod 7, y ^ 4 - y ^ 2 + 1 ≠ 0 := by decide

theorem no_root5_phi9 : ∀ y : ZMod 5, y ^ 6 + y ^ 3 + 1 ≠ 0 := by decide

theorem no_root7_phi9 : ∀ y : ZMod 7, y ^ 6 + y ^ 3 + 1 ≠ 0 := by decide

theorem no_root5_phi18 : ∀ y : ZMod 5, y ^ 6 - y ^ 3 + 1 ≠ 0 := by decide

theorem no_root7_phi18 : ∀ y : ZMod 7, y ^ 6 - y ^ 3 + 1 ≠ 0 := by decide

theorem e6Eight_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : (p : ℤ) ∣ (q : ℤ) ^ 4 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 8 := by
  have hx : (q : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 4 + 1) p).2 h
    simpa using this
  have hp7 : 7 < p := by
    by_contra hle
    rcases eq_five_or_seven hp hp3 (by omega) with rfl | rfl
    · exact no_root5_phi8 _ hx
    · exact no_root7_phi8 _ hx
  refine ⟨hp7, ?_, ?_⟩
  · intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    simp at hx
  · obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
    rw [← hxdef] at hx ⊢
    have h8 : x ^ 8 = 1 := by linear_combination (x ^ 4 - 1) * hx
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h8 fun ℓ hℓ hdvd => ?_
    obtain rfl := prime_dvd_eight hℓ hdvd
    intro h4
    have h4' : x ^ 4 = 1 := by simpa using h4
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx - h4'
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) h2

theorem e6Eight_factors {p q : ℕ} (hord : orderOf (q : ZMod p) = 8) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 ∧ ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧ ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 := by
  have hne := pow_ne_one_of_orderOf hord (show ¬ 8 ∣ 4 by norm_num)
  exact ⟨not_dvd_of_pow_ne_one hne (Q := (q : ℤ) ^ 2 + 1) (by ring),
    not_dvd_of_pow_ne_one hne (Q := ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + 1)) (by ring),
    not_dvd_of_pow_ne_one hne (Q := (q : ℤ) ^ 2 - 1) (by ring)⟩

theorem e6Twelve_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 12 := by
  have hx : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) p).2 h
    simpa using this
  have hp7 : 7 < p := by
    by_contra hle
    rcases eq_five_or_seven hp hp3 (by omega) with rfl | rfl
    · exact no_root5_phi12 _ hx
    · exact no_root7_phi12 _ hx
  refine ⟨hp7, ?_, ?_⟩
  · intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    simp at hx
  · obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
    rw [← hxdef] at hx ⊢
    have h12 : x ^ 12 = 1 := by
      linear_combination ((x - 1) * (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 + 1) * (x ^ 2 - x + 1)) * hx
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h12 fun ℓ hℓ hdvd => ?_
    rcases prime_dvd_twelve hℓ hdvd with rfl | rfl
    · intro h6
      have h6' : x ^ 6 = 1 := by simpa using h6
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination (x ^ 2 + 1) * hx - h6'
      exact natCast_ne_zero_of_lt (by norm_num) (by omega) h2
    · intro h4
      have h4' : x ^ 4 = 1 := by simpa using h4
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination (x ^ 2 + 2) * hx - (x ^ 2 + 1) * h4'
      exact natCast_ne_zero_of_lt (by norm_num) (by omega) h3

theorem e6Twelve_factors {p q : ℕ} (hp : p.Prime) (hord : orderOf (q : ZMod p) = 12) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1 ∧ ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧
      ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 2 + 1) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h6 := pow_ne_one_of_orderOf hord (show ¬ 12 ∣ 6 by norm_num)
  have h4 := pow_ne_one_of_orderOf hord (show ¬ 12 ∣ 4 by norm_num)
  have hg : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1 :=
    not_dvd_of_pow_ne_one h6 (Q := ((q : ℤ) - 1) * ((q : ℤ) ^ 3 + 1)) (by ring)
  have h1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 :=
    not_dvd_of_pow_ne_one h6 (Q := ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 3 + 1)) (by ring)
  have h3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 3 + 1 :=
    not_dvd_of_pow_ne_one h6 (Q := (q : ℤ) ^ 3 - 1) (by ring)
  have h2 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 :=
    not_dvd_of_pow_ne_one h4 (Q := (q : ℤ) ^ 2 - 1) (by ring)
  exact ⟨hg, h1, hpz.not_dvd_mul (hpz.not_dvd_mul h1 h3) h2⟩

theorem e6Nine_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 9 := by
  have hx : (q : ZMod p) ^ 6 + (q : ZMod p) ^ 3 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 + (q : ℤ) ^ 3 + 1) p).2 h
    simpa using this
  have hp7 : 7 < p := by
    by_contra hle
    rcases eq_five_or_seven hp hp3 (by omega) with rfl | rfl
    · exact no_root5_phi9 _ hx
    · exact no_root7_phi9 _ hx
  refine ⟨hp7, ?_, ?_⟩
  · intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    simp at hx
  · obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
    rw [← hxdef] at hx ⊢
    have h9 : x ^ 9 = 1 := by linear_combination (x ^ 3 - 1) * hx
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h9 fun ℓ hℓ hdvd => ?_
    obtain rfl := prime_dvd_nine hℓ hdvd
    intro h3
    have h3' : x ^ 3 = 1 := by simpa using h3
    have h3z : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx - (x ^ 3 + 2) * h3'
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) h3z

theorem e6Nine_factors {p q : ℕ} (hord : orderOf (q : ZMod p) = 9) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ 3 - 1 :=
  not_dvd_of_pow_ne_one (pow_ne_one_of_orderOf hord (show ¬ 9 ∣ 3 by norm_num)) (Q := 1)
    (by ring)

theorem e7Nine_factors {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hord : orderOf (q : ZMod p) = 9) :
    ¬ (p : ℤ) ∣ (q : ℤ) - 1 ∧
      ¬ (p : ℤ) ∣ ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 9 + 1) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h3 := pow_ne_one_of_orderOf hord (show ¬ 9 ∣ 3 by norm_num)
  have h1 : ¬ (p : ℤ) ∣ (q : ℤ) - 1 :=
    not_dvd_of_pow_ne_one h3 (Q := (q : ℤ) ^ 2 + (q : ℤ) + 1) (by ring)
  have h2 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + (q : ℤ) + 1 :=
    not_dvd_of_pow_ne_one h3 (Q := (q : ℤ) - 1) (by ring)
  have h4 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 9 + 1 := by
    intro hd
    have h9 : (q : ZMod p) ^ 9 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
    push_cast at h0
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h0 - h9
    exact natCast_ne_zero_of_lt (by norm_num) (by omega) h2'
  exact ⟨h1, hpz.not_dvd_mul h2 h4⟩

theorem e7Eighteen_data {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 - (q : ℤ) ^ 3 + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 18 := by
  have hx : (q : ZMod p) ^ 6 - (q : ZMod p) ^ 3 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 - (q : ℤ) ^ 3 + 1) p).2 h
    simpa using this
  have hp7 : 7 < p := by
    by_contra hle
    rcases eq_five_or_seven hp hp3 (by omega) with rfl | rfl
    · exact no_root5_phi18 _ hx
    · exact no_root7_phi18 _ hx
  refine ⟨hp7, ?_, ?_⟩
  · intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    simp at hx
  · obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
    rw [← hxdef] at hx ⊢
    have h18 : x ^ 18 = 1 := by linear_combination ((x ^ 9 - 1) * (x ^ 3 + 1)) * hx
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h18 fun ℓ hℓ hdvd => ?_
    rcases prime_dvd_eighteen hℓ hdvd with rfl | rfl
    · intro h9
      have h9' : x ^ 9 = 1 := by simpa using h9
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination (x ^ 3 + 1) * hx - h9'
      exact natCast_ne_zero_of_lt (by norm_num) (by omega) h2
    · intro h6
      have h6' : x ^ 6 = 1 := by simpa using h6
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination (x ^ 3 + 2) * hx - (x ^ 3 + 1) * h6'
      exact natCast_ne_zero_of_lt (by norm_num) (by omega) h3

theorem e7Eighteen_factors {p q : ℕ} (hp : p.Prime) (hord : orderOf (q : ZMod p) = 18) :
    ¬ (p : ℤ) ∣ (q : ℤ) + 1 ∧
      ¬ (p : ℤ) ∣ ((q : ℤ) ^ 9 - 1) * ((q : ℤ) ^ 2 - (q : ℤ) + 1) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h6 := pow_ne_one_of_orderOf hord (show ¬ 18 ∣ 6 by norm_num)
  have h9 := pow_ne_one_of_orderOf hord (show ¬ 18 ∣ 9 by norm_num)
  have h1 : ¬ (p : ℤ) ∣ (q : ℤ) + 1 :=
    not_dvd_of_pow_ne_one h6
      (Q := ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 2 - (q : ℤ) + 1)) (by ring)
  have h2 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1 :=
    not_dvd_of_pow_ne_one h6
      (Q := ((q : ℤ) - 1) * ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + (q : ℤ) + 1)) (by ring)
  have h3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 9 - 1 := not_dvd_of_pow_ne_one h9 (Q := 1) (by ring)
  exact ⟨h1, hpz.not_dvd_mul h3 h2⟩

end CFSG.RankThree.PartOne.KE.CTE6
