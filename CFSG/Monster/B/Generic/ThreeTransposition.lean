module

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

namespace CFSG.Monster.B.Generic

variable {L : Type*} [Group L]

theorem mul_self_eq_one_of_orderOf_eq_two {x : L} (h : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem braid_of_pow_three_eq_one {t a : L} (ht : t * t = 1) (ha : a * a = 1)
    (h3 : (t * a) ^ 3 = 1) : a * t * a = t * a * t := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h3' : t * a * t * a * t * a = 1 := by
    rw [← h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc a * t * a = t⁻¹ * (t * a * t * a * t * a) * a⁻¹ * t⁻¹ := by group
    _ = t * a * t := by rw [h3', ht', ha']; group

theorem pow_four_eq_one_of_braid {a b t : L} (ha : a * a = 1) (hb : b * b = 1)
    (ht : t * t = 1) (hab : a * b = b * a) (hata : a * t * a = t * a * t)
    (hbtb : b * t * b = t * b * t) : (a * b * t) ^ 4 = 1 := by
  have hbX : ∀ X : L, b * (b * X) = X := fun X => by rw [← mul_assoc, hb, one_mul]
  have htX : ∀ X : L, t * (t * X) = X := fun X => by rw [← mul_assoc, ht, one_mul]
  have habX : ∀ X : L, a * (b * X) = b * (a * X) := fun X => by
    rw [← mul_assoc, hab, mul_assoc]
  have hataX : ∀ X : L, a * (t * (a * X)) = t * (a * (t * X)) := fun X => by
    rw [← mul_assoc, ← mul_assoc, hata, mul_assoc, mul_assoc]
  have hbtbX : ∀ X : L, b * (t * (b * X)) = t * (b * (t * X)) := fun X => by
    rw [← mul_assoc, ← mul_assoc, hbtb, mul_assoc, mul_assoc]
  have E1X : ∀ X : L, a * (b * (t * (a * (b * (t * X))))) =
      a * (t * (b * (t * (a * (t * X))))) := fun X => by
    rw [habX (t * X), hbtbX (a * (t * X))]
  have E1 : a * (b * (t * (a * (b * t)))) = a * (t * (b * (t * (a * t)))) := by
    simpa using E1X 1
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [E1X (a * (b * (t * (a * (b * t))))), E1, hataX (t * (b * (t * (a * t)))),
    htX (a * (t * (t * (b * (t * (a * t)))))), htX (b * (t * (a * t))),
    ← habX (b * (t * (a * t))), hbX (t * (a * t)), hataX t, htX, ht, mul_one, ha]

theorem not_commute_of_orderOf_mul_eq_three {t a : L} (ht : t * t = 1) (ha : a * a = 1)
    (h3 : orderOf (t * a) = 3) : ¬ Commute t a := by
  intro hc
  have h2 : (t * a) ^ 2 = 1 := by rw [hc.mul_pow, pow_two, pow_two, ht, ha, one_mul]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h3] at this
  norm_num at this

theorem not_commute_mul_of_pow_three {t a b : L} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (hne : a ≠ b) (h3a : (t * a) ^ 3 = 1) (h3b : (t * b) ^ 3 = 1) :
    ¬ Commute t (a * b) := by
  intro hc
  have hca : Commute (t * a) (a * b) := hc.mul_left ((Commute.refl a).mul_right hab)
  have htb : t * b = t * a * (a * b) := by
    rw [mul_assoc, ← mul_assoc a a b, ha, one_mul]
  have hc2 : a * b * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc b a b, ← hab.eq, mul_assoc, hb, mul_one, ha]
  have hc3 : (t * b) ^ 3 = a * b := by
    rw [htb, hca.mul_pow, h3a, one_mul, pow_succ, pow_two, hc2, one_mul]
  rw [h3b] at hc3
  apply hne
  have h1 : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp hc3.symm
  rw [h1, inv_eq_of_mul_eq_one_right hb]

theorem not_commute_mul_mul_of_pow_three {t a b c : L} (ht : t * t = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (h3a : (t * a) ^ 3 = 1) (h3b : (t * b) ^ 3 = 1)
    (h3c : orderOf (t * c) = 3) : ¬ Commute t (a * b * c) := by
  intro hr
  set r := a * b * c with hr_def
  have hra : Commute r a := ((Commute.refl a).mul_left hab.symm).mul_left hac.symm
  have hrb : Commute r b := (hab.mul_left (Commute.refl b)).mul_left hbc.symm
  have hrt : Commute r (t * a * b) := (hr.symm.mul_right hra).mul_right hrb
  have hr2 : r * r = 1 := by
    have : r * r = (a * a) * (b * b) * (c * c) := by
      simp only [hr_def]
      rw [show a * b * c * (a * b * c) = a * (b * (c * a)) * (b * c) by group, ← hac.eq,
        show a * (b * (a * c)) * (b * c) = a * (b * a) * (c * b) * c by group, ← hab.eq,
        ← hbc.eq]
      group
    rw [this, ha, hb, hc, one_mul, one_mul]
  have hcr : c = a * b * r := by
    simp only [hr_def]
    rw [show a * b * (a * b * c) = a * (b * a) * b * c by group, ← hab.eq,
      show a * (a * b) * b * c = (a * a) * (b * b) * c by group, ha, hb, one_mul, one_mul]
  have htc : t * c = t * a * b * r := by rw [hcr]; group
  have h3' : (t * a * b) ^ 3 * r = 1 := by
    have h := pow_orderOf_eq_one (t * c)
    rw [h3c, htc, hrt.symm.mul_pow] at h
    rwa [pow_succ r 2, pow_two, hr2, one_mul] at h
  have h4 : (t * a * b) ^ 4 = 1 := by
    have hconj : t * a * b = t * (a * b * t) * t⁻¹ := by group
    rw [hconj, conj_pow, pow_four_eq_one_of_braid ha hb ht hab.eq
      (braid_of_pow_three_eq_one ht ha h3a) (braid_of_pow_three_eq_one ht hb h3b)]
    group
  have hy : t * a * b = r := by
    have hr' : r = ((t * a * b) ^ 3)⁻¹ := (mul_eq_one_iff_inv_eq.mp h3').symm
    rw [hr']
    calc t * a * b = (t * a * b) ^ 4 * ((t * a * b) ^ 3)⁻¹ := by group
      _ = ((t * a * b) ^ 3)⁻¹ := by rw [h4, one_mul]
  have htc' : t = c := by
    have : t = r * (b * a) := by
      rw [← hy, mul_assoc, mul_assoc, ← mul_assoc b b a, hb, one_mul, ha, mul_one]
    rw [this, hr_def, show a * b * c * (b * a) = a * (b * c) * b * a by group, hbc.eq,
      show a * (c * b) * b * a = a * c * (b * b) * a by group, hb, mul_one, hac.eq,
      mul_assoc, ha, mul_one]
  have h1 : orderOf (t * c) = 1 := by rw [htc', hc, orderOf_one]
  omega

theorem three_transpositions_short_commuting_products {L : Type*} [Group L] {t : L}
    (ht : orderOf t = 2) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (a : Fin k → L)
    (hinj : Function.Injective a) (hcomm : ∀ i j, Commute (a i) (a j))
    (hinv : ∀ i, orderOf (a i) = 2) (h3 : ∀ i, orderOf (t * a i) = 3) :
    ¬ Commute t (List.ofFn a).prod := by
  have ht' := mul_self_eq_one_of_orderOf_eq_two ht
  have ha i := mul_self_eq_one_of_orderOf_eq_two (hinv i)
  have h3' i : (t * a i) ^ 3 = 1 := by rw [← h3 i, pow_orderOf_eq_one]
  interval_cases k
  · simpa using not_commute_of_orderOf_mul_eq_three ht' (ha 0) (h3 0)
  · simpa using not_commute_mul_of_pow_three (ha 0) (ha 1) (hcomm 0 1)
      (fun h => absurd (hinj h) (by decide)) (h3' 0) (h3' 1)
  · simpa [mul_assoc] using not_commute_mul_mul_of_pow_three ht' (ha 0) (ha 1) (ha 2)
      (hcomm 0 1) (hcomm 0 2) (hcomm 1 2) (h3' 0) (h3' 1) (h3 2)

end CFSG.Monster.B.Generic
