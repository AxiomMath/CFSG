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
public import Mathlib.GroupTheory.Nilpotent
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

namespace Involutions

variable {X : Type*} [Group X] {a b : X}

theorem conj_mul (ha : a * a = 1) (hb : b * b = 1) : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right ha, mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hb, ← mul_assoc, ha, one_mul]

theorem mul_zpow (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    a * (a * b) ^ i = (a * b) ^ (-i) * a := by
  have h2 : a * (a * b) ^ i * a⁻¹ = (a * b) ^ (-i) := by
    rw [← conj_zpow, conj_mul ha hb, zpow_neg, inv_zpow]
  calc a * (a * b) ^ i = a * (a * b) ^ i * a⁻¹ * a := by group
    _ = (a * b) ^ (-i) * a := by rw [h2]

theorem inv_mul_self_mul (hb : b * b = 1) : (a * b)⁻¹ * a = b := by
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_eq_of_mul_eq_one_right hb]

theorem conj_zpow_left (ha : a * a = 1) (hb : b * b = 1) (j : ℤ) :
    (a * b) ^ j * a * ((a * b) ^ j)⁻¹ = (a * b) ^ (2 * j) * a := by
  rw [← zpow_neg, mul_assoc, mul_zpow ha hb, neg_neg, ← mul_assoc, ← zpow_add, two_mul]

theorem conj_zpow_right (ha : a * a = 1) (hb : b * b = 1) (j : ℤ) :
    (a * b) ^ j * b * ((a * b) ^ j)⁻¹ = (a * b) ^ (2 * j - 1) * a := by
  have e : (a * b) ^ j * b = (a * b) ^ (j - 1) * a := by
    rw [zpow_sub_one, mul_assoc, inv_mul_self_mul hb]
  rw [e, ← zpow_neg, mul_assoc, mul_zpow ha hb, neg_neg, ← mul_assoc, ← zpow_add]
  congr 2
  ring

theorem zpow_mul_mul_self (ha : a * a = 1) (hb : b * b = 1) (i : ℤ) :
    (a * b) ^ i * a * ((a * b) ^ i * a) = 1 := by
  rw [mul_assoc, ← mul_assoc a, mul_zpow ha hb, mul_assoc, ha, mul_one, ← zpow_add,
    add_neg_cancel, zpow_zero]

theorem commute_zpow_of_zpow_two_mul (ha : a * a = 1) (hb : b * b = 1) {r : ℤ}
    (h : (a * b) ^ (2 * r) = 1) :
    a * (a * b) ^ r = (a * b) ^ r * a ∧ b * (a * b) ^ r = (a * b) ^ r * b := by
  have hr : (a * b) ^ (-r) = (a * b) ^ r := by
    rw [zpow_neg, inv_eq_iff_mul_eq_one, ← zpow_add, ← two_mul, h]
  have h1 : a * (a * b) ^ r = (a * b) ^ r * a := by rw [mul_zpow ha hb, hr]
  refine ⟨h1, ?_⟩
  calc b * (a * b) ^ r = (a * b)⁻¹ * a * (a * b) ^ r := by rw [inv_mul_self_mul hb]
    _ = (a * b)⁻¹ * ((a * b) ^ r * a) := by rw [mul_assoc, h1]
    _ = (a * b) ^ r * ((a * b)⁻¹ * a) := by
      rw [← mul_assoc, ← mul_assoc, ← zpow_neg_one, zpow_mul_comm]
    _ = (a * b) ^ r * b := by rw [inv_mul_self_mul hb]

theorem mem_closure_pair (ha : a * a = 1) (hb : b * b = 1) {g : X}
    (hg : g ∈ Subgroup.closure ({a, b} : Set X)) :
    ∃ i : ℤ, g = (a * b) ^ i ∨ g = (a * b) ^ i * a := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, inv_mul_self_mul hb]
  | one => exact ⟨0, Or.inl (zpow_zero _).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨j, rfl | rfl⟩ := hy
    · exact ⟨i + j, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨i - j, Or.inr ?_⟩
      rw [mul_assoc, mul_zpow ha hb, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨i - j, Or.inl ?_⟩
      rw [mul_assoc, ← mul_assoc a, mul_zpow ha hb, mul_assoc, ha, mul_one, ← zpow_add,
        sub_eq_add_neg]
  | inv x _ hx =>
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact ⟨-i, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, ← zpow_neg, mul_zpow ha hb, neg_neg]

theorem isPGroup_closure_pair (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : (a * b) ^ 2 ^ k = 1) : IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) := by
  rintro ⟨g, hg⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  obtain ⟨i, rfl | rfl⟩ := mem_closure_pair ha hb hg
  · have h1 : ((a * b) ^ i) ^ 2 ^ k = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, hk, one_zpow]
    rw [pow_succ, pow_mul, h1, one_pow]
  · rw [pow_succ', pow_mul, pow_two, zpow_mul_mul_self ha hb, one_pow]

theorem exists_zpow_conj_of_odd (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) : ∃ j : ℤ, (a * b) ^ j * a * ((a * b) ^ j)⁻¹ = b := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  have hpow : (a * b) ^ ((2 * k + 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hk, pow_orderOf_eq_one]
  have e : (a * b) ^ (2 * (k : ℤ)) = (a * b) ^ ((2 * k + 1 : ℕ) : ℤ) * (a * b)⁻¹ := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    push_cast
    ring
  rw [conj_zpow_left ha hb, e, hpow, one_mul, inv_mul_self_mul hb]

end Involutions

namespace StrongClosure

variable {X : Type*} [Group X]

@[expose] def dBar (D₀ : Set X) : Set X := {x | ∃ g : X, ∃ a ∈ D₀, g * a * g⁻¹ = x}

theorem conj_mul_conj (y c x : X) : y * c * x * (y * c)⁻¹ = y * (c * x * c⁻¹) * y⁻¹ := by
  group

end StrongClosure

open StrongClosure

variable {X : Type*} [Group X]

theorem mem_of_inv_conj_mem_of_commute [Finite X] {V : Subgroup X} {D₀ : Set X}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hD₀V : D₀ ⊆ V) (hD₀ : D₀.Nonempty)
    (h1 : ∀ g k : X, ∀ a ∈ D₀, ∀ b ∈ D₀,
      g * a * g⁻¹ * (k * b * k⁻¹) = k * b * k⁻¹ * (g * a * g⁻¹) →
        g⁻¹ * k ∈ Subgroup.normalizer (V : Set X))
    (h4 : ∀ a ∈ dBar D₀, ∀ b ∈ dBar D₀,
      IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) → a * b = b * a)
    {c w : X} (hw : c⁻¹ * w * c ∈ V) {a : X} (ha : a ∈ D₀) (haw : a * w = w * a) : w ∈ V := by
  obtain ⟨b₀, hb₀⟩ := hD₀
  obtain ⟨b, hbc⟩ : ∃ b : X, c * b₀ * c⁻¹ = b := ⟨_, rfl⟩
  have ha2 : a * a = 1 := hV2 a (hD₀V ha)
  have hb2 : b * b = 1 := by
    rw [← hbc]
    calc c * b₀ * c⁻¹ * (c * b₀ * c⁻¹) = c * (b₀ * b₀) * c⁻¹ := by group
      _ = 1 := by rw [hV2 b₀ (hD₀V hb₀), mul_one, mul_inv_cancel]
  have hbw : b * w = w * b := by
    rw [← hbc]
    have e := hVab b₀ (hD₀V hb₀) _ hw
    calc c * b₀ * c⁻¹ * w = c * (b₀ * (c⁻¹ * w * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * w * c) * b₀) * c⁻¹ := by rw [e]
      _ = w * (c * b₀ * c⁻¹) := by group
  suffices H : ∃ h : X, h * w = w * h ∧ h * c ∈ Subgroup.normalizer (V : Set X) by
    obtain ⟨h, hhw, hhc⟩ := H
    have hmem := (Subgroup.mem_normalizer_iff.1 hhc (c⁻¹ * w * c)).1 hw
    have e : h * c * (c⁻¹ * w * c) * (h * c)⁻¹ = w := by
      calc h * c * (c⁻¹ * w * c) * (h * c)⁻¹ = h * w * h⁻¹ := by group
        _ = w := by rw [hhw, mul_inv_cancel_right]
    rwa [e] at hmem
  have hcomm : Commute (a * b) w := Commute.mul_left haw hbw
  have haD : a ∈ dBar D₀ := ⟨1, a, ha, by group⟩
  have hconjb : ∀ j : ℤ, (a * b) ^ j * c * b₀ * ((a * b) ^ j * c)⁻¹ =
      (a * b) ^ j * b * ((a * b) ^ j)⁻¹ := fun j => by rw [conj_mul_conj, hbc]
  have hmpos : 0 < orderOf (a * b) := orderOf_pos _
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨r, hr⟩ | hodd
  · rcases Nat.even_or_odd r with ⟨q, hq⟩ | ⟨j, hj⟩
    ·
      exfalso
      have hqpos : 0 < q := by omega
      have hb'2 := Involutions.zpow_mul_mul_self ha2 hb2 (q : ℤ)
      have hab' : a * ((a * b) ^ (q : ℤ) * a) = (a * b) ^ (-(q : ℤ)) := by
        rw [← mul_assoc, Involutions.mul_zpow ha2 hb2, mul_assoc, ha2, mul_one]
      have h4pow : (a * ((a * b) ^ (q : ℤ) * a)) ^ 2 ^ 2 = 1 := by
        rw [hab', ← zpow_natCast, ← zpow_mul,
          show -(q : ℤ) * ((2 ^ 2 : ℕ) : ℤ) = -((orderOf (a * b) : ℕ) : ℤ) by push_cast; omega,
          zpow_neg, zpow_natCast, pow_orderOf_eq_one, inv_one]
      have hb'D : (a * b) ^ (q : ℤ) * a ∈ dBar D₀ := by
        rcases Int.even_or_odd (q : ℤ) with ⟨p, hp⟩ | ⟨p, hp⟩
        · refine ⟨(a * b) ^ p, a, ha, ?_⟩
          rw [Involutions.conj_zpow_left ha2 hb2 p, hp, two_mul]
        · refine ⟨(a * b) ^ (p + 1) * c, b₀, hb₀, ?_⟩
          rw [hconjb, Involutions.conj_zpow_right ha2 hb2, hp]
          congr 2
          ring
      have hcomm' := h4 a haD _ hb'D (Involutions.isPGroup_closure_pair ha2 hb'2 h4pow)
      have hsq : a * ((a * b) ^ (q : ℤ) * a) * (a * ((a * b) ^ (q : ℤ) * a)) = 1 := by
        calc a * ((a * b) ^ (q : ℤ) * a) * (a * ((a * b) ^ (q : ℤ) * a)) =
            a * (((a * b) ^ (q : ℤ) * a) * a) * ((a * b) ^ (q : ℤ) * a) := by group
          _ = a * (a * ((a * b) ^ (q : ℤ) * a)) * ((a * b) ^ (q : ℤ) * a) := by rw [← hcomm']
          _ = 1 := by rw [← mul_assoc a a, ha2, one_mul, hb'2]
      rw [hab', ← zpow_add, show -(q : ℤ) + -(q : ℤ) = -((q + q : ℕ) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, inv_eq_one] at hsq
      have hdvd := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hsq)
      omega
    ·
      have h2r : (a * b) ^ (2 * (r : ℤ)) = 1 := by
        rw [show 2 * (r : ℤ) = ((orderOf (a * b) : ℕ) : ℤ) by omega, zpow_natCast,
          pow_orderOf_eq_one]
      have hcen := (Involutions.commute_zpow_of_zpow_two_mul ha2 hb2 h2r).1
      refine ⟨(a * b) ^ ((j : ℤ) + 1), (hcomm.zpow_left _).eq, ?_⟩
      have hN := h1 1 ((a * b) ^ ((j : ℤ) + 1) * c) a ha b₀ hb₀ (by
        rw [one_mul, inv_one, mul_one, hconjb, Involutions.conj_zpow_right ha2 hb2,
          show 2 * ((j : ℤ) + 1) - 1 = (r : ℤ) by omega, ← mul_assoc, hcen])
      rwa [inv_one, one_mul] at hN
  ·
    obtain ⟨j, hj⟩ := Involutions.exists_zpow_conj_of_odd ha2 hb2 hodd
    refine ⟨((a * b) ^ j)⁻¹, ((hcomm.zpow_left j).inv_left).eq, ?_⟩
    exact h1 ((a * b) ^ j) c a ha b₀ hb₀ (by rw [hj, hbc])

theorem conj_mem_of_conj_mem_normalizer [Finite X] {V : Subgroup X} {D₀ : Set X}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hD₀V : D₀ ⊆ V)
    (h1 : ∀ g k : X, ∀ a ∈ D₀, ∀ b ∈ D₀,
      g * a * g⁻¹ * (k * b * k⁻¹) = k * b * k⁻¹ * (g * a * g⁻¹) →
        g⁻¹ * k ∈ Subgroup.normalizer (V : Set X))
    (h4 : ∀ a ∈ dBar D₀, ∀ b ∈ dBar D₀,
      IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) → a * b = b * a)
    (hFP : ∀ w ∈ Subgroup.normalizer (V : Set X), w * w = 1 → w ∉ V → ∃ a ∈ D₀, a * w = w * a)
    {x : X} (hx : x ∈ V) (c : X) (hcx : c * x * c⁻¹ ∈ Subgroup.normalizer (V : Set X)) :
    c * x * c⁻¹ ∈ V := by
  by_contra hw
  have hw2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hV2 x hx, mul_one, mul_inv_cancel]
  obtain ⟨a, ha, haw⟩ := hFP _ hcx hw2 hw
  refine hw (mem_of_inv_conj_mem_of_commute hVab hV2 hD₀V ⟨a, ha⟩ h1 h4 (c := c) ?_ ha haw)
  rw [show c⁻¹ * (c * x * c⁻¹) * c = x by group]
  exact hx

theorem strongly_closed_of_le_normalizer [Finite X] {V : Subgroup X} {D₀ : Set X}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hD₀V : D₀ ⊆ V)
    (h1 : ∀ g k : X, ∀ a ∈ D₀, ∀ b ∈ D₀,
      g * a * g⁻¹ * (k * b * k⁻¹) = k * b * k⁻¹ * (g * a * g⁻¹) →
        g⁻¹ * k ∈ Subgroup.normalizer (V : Set X))
    (h4 : ∀ a ∈ dBar D₀, ∀ b ∈ dBar D₀,
      IsPGroup 2 (Subgroup.closure ({a, b} : Set X)) → a * b = b * a)
    (hFP : ∀ w ∈ Subgroup.normalizer (V : Set X), w * w = 1 → w ∉ V → ∃ a ∈ D₀, a * w = w * a)
    {S : Subgroup X} (hS : S ≤ Subgroup.normalizer (V : Set X)) :
    ∀ a ∈ V, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ V := by
  intro a ha g hg
  have e : g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ := by rw [inv_inv]
  rw [e] at hg ⊢
  exact conj_mem_of_conj_mem_normalizer hVab hV2 hD₀V h1 h4 hFP ha g⁻¹ (hS hg)

end CFSG.Monster.B.Recog
