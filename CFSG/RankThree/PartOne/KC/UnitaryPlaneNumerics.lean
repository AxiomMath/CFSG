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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

@[expose] noncomputable def ordNegQ (ℓ f p : ℕ) : ℕ := orderOf (-((ℓ : ZMod p) ^ f))

variable {ℓ f p : ℕ}

theorem natCast_pow_ne_zero (hp : p.Prime) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime) :
    ((ℓ : ZMod p) ^ f) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  refine pow_ne_zero _ fun h => ?_
  have h1 := (ZMod.natCast_eq_zero_iff ℓ p).mp h
  exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h1)

theorem ordNegQ_eq_one_iff (hp : p.Prime) :
    ordNegQ ℓ f p = 1 ↔ p ∣ ℓ ^ f + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold ordNegQ
  rw [orderOf_eq_one_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

theorem ordNegQ_dvd_sub_one (hp : p.Prime) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime) :
    ordNegQ ℓ f p ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold ordNegQ
  exact ZMod.orderOf_dvd_card_sub_one (neg_ne_zero.mpr (natCast_pow_ne_zero hp hpℓ hℓ))

theorem coprime_ordNegQ (hp : p.Prime) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime) :
    Nat.Coprime (ordNegQ ℓ f p) p := by
  have h1 := ordNegQ_dvd_sub_one (f := f) hp hpℓ hℓ
  refine Nat.Coprime.coprime_dvd_left h1 ?_
  have h3 : Nat.Coprime (p - 1) (p - 1 + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rwa [Nat.sub_add_cancel hp.one_lt.le] at h3

theorem pos_ordNegQ (hp : p.Prime) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime) : 0 < ordNegQ ℓ f p :=
  Nat.pos_of_dvd_of_pos (ordNegQ_dvd_sub_one hp hpℓ hℓ) (by have := hp.two_le; omega)

theorem dvd_of_ordNegQ_eq (hp : p.Prime) {k : ℕ} (hk : ordNegQ ℓ f p = k) :
    (p : ℤ) ∣ (-((ℓ ^ f : ℕ) : ℤ)) ^ k - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (-((ℓ : ZMod p) ^ f)) ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact sub_eq_zero.mpr h1

theorem ordNegQ_eq_two (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (h2 : ordNegQ ℓ f p = 2) (hf : 1 ≤ f) : p ∣ ℓ ^ f - 1 ∧ 3 < ℓ ^ f := by
  have hne : ordNegQ ℓ f p ≠ 1 := by omega
  have hd := dvd_of_ordNegQ_eq hp h2
  have hq1 : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 := by
    simpa [neg_sq] using hd
  have hfac : ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 =
      (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by ring
  rw [hfac] at hd'
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : ¬ p ∣ ℓ ^ f + 1 := fun h => hne ((ordNegQ_eq_one_iff hp).mpr h)
  rcases hpz.dvd_or_dvd hd' with h | h
  · have h' : p ∣ ℓ ^ f - 1 := by
      have : ((ℓ ^ f - 1 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub hq1.le]
        simp
      rw [← this] at h
      exact_mod_cast h
    refine ⟨h', ?_⟩
    have := Nat.le_of_dvd (by omega) h'
    omega
  · exfalso
    apply hp1
    have : ((ℓ ^ f + 1 : ℕ) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [← this] at h
    exact_mod_cast h

theorem four_le_ordNegQ_of_two (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime)
    (hq : ℓ ^ f = 2) : 4 ≤ ordNegQ ℓ f p := by
  have hpos := pos_ordNegQ (f := f) hp hpℓ hℓ
  by_contra hlt
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hcases : ordNegQ ℓ f p = 1 ∨ ordNegQ ℓ f p = 2 ∨ ordNegQ ℓ f p = 3 := by omega
  rcases hcases with h | h | h
  · have hd := dvd_of_ordNegQ_eq hp h
    rw [hq] at hd
    norm_num at hd
    have : p ∣ 3 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have hd := dvd_of_ordNegQ_eq hp h
    rw [hq] at hd
    norm_num at hd
    have : p ∣ 3 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have hd := dvd_of_ordNegQ_eq hp h
    rw [hq] at hd
    norm_num at hd
    have h9 : p ∣ 9 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) h9
    interval_cases p <;> first | omega | (exact absurd hp (by norm_num))

theorem three_le_ordNegQ_of_three (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hℓ : ℓ.Prime)
    (hq : ℓ ^ f = 3) : 3 ≤ ordNegQ ℓ f p := by
  have hpos := pos_ordNegQ (f := f) hp hpℓ hℓ
  by_contra hlt
  have hcases : ordNegQ ℓ f p = 1 ∨ ordNegQ ℓ f p = 2 := by omega
  rcases hcases with h | h
  · have hd := dvd_of_ordNegQ_eq hp h
    rw [hq] at hd
    norm_num at hd
    have h4 : p ∣ 4 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) h4
    interval_cases p
    exact absurd hp (by norm_num)
  · have hd := dvd_of_ordNegQ_eq hp h
    rw [hq] at hd
    norm_num at hd
    have h8 : p ∣ 8 := by exact_mod_cast hd
    have := Nat.le_of_dvd (by norm_num) h8
    interval_cases p <;> first | omega | (exact absurd hp (by norm_num))

end CFSG.RankThree.PartOne.KCUnitaryPlane
