module

public import Mathlib.Algebra.Group.MinimalAxioms
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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

namespace Baer

variable {H : Type*} [Group H]

def baerAdd (m : ℕ) (g h : H) : H := g * h * ⁅h, g⁆ ^ m

theorem baerAdd_def (m : ℕ) (g h : H) : baerAdd m g h = g * h * ⁅h, g⁆ ^ m := by
  rw [baerAdd]

theorem commute_of_mem_center {z : H} (hz : z ∈ Subgroup.center H) (a : H) : Commute z a :=
  (Subgroup.mem_center_iff.mp hz a).symm

theorem commutator_mul_right (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H) (a b c : H) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hbc := Subgroup.mem_center_iff.mp (hcen a c) b
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by simp only [mul_assoc]
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b) * b⁻¹ := by rw [hbc]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by group

theorem commutator_mul_left (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H) (a b c : H) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp (hcen b c) a,
    mul_inv_cancel_right]
  exact Subgroup.mem_center_iff.mp (hcen a c) _

theorem commutator_eq_one_of_mem_center_right {z : H} (hz : z ∈ Subgroup.center H) (a : H) :
    ⁅a, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)

theorem commutator_eq_one_of_mem_center_left {z : H} (hz : z ∈ Subgroup.center H) (a : H) :
    ⁅z, a⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a).symm

theorem commutator_baerAdd_left (m : ℕ) (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H)
    (g h f : H) : ⁅baerAdd m g h, f⁆ = ⁅g, f⁆ * ⁅h, f⁆ := by
  rw [baerAdd_def, commutator_mul_left hcen, commutator_mul_left hcen,
    commutator_eq_one_of_mem_center_left (Subgroup.pow_mem _ (hcen h g) m) f, mul_one]

theorem commutator_baerAdd_right (m : ℕ) (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H)
    (f g h : H) : ⁅f, baerAdd m g h⁆ = ⁅f, g⁆ * ⁅f, h⁆ := by
  rw [baerAdd_def, commutator_mul_right hcen, commutator_mul_right hcen,
    commutator_eq_one_of_mem_center_right (Subgroup.pow_mem _ (hcen h g) m) f, mul_one]

theorem baerAdd_assoc (m : ℕ) (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H) (g h f : H) :
    baerAdd m (baerAdd m g h) f = baerAdd m g (baerAdd m h f) := by
  rw [baerAdd_def m (baerAdd m g h) f, baerAdd_def m g (baerAdd m h f),
    commutator_baerAdd_right m hcen, commutator_baerAdd_left m hcen,
    (commute_of_mem_center (hcen f g) _).mul_pow, (commute_of_mem_center (hcen h g) _).mul_pow,
    baerAdd_def m g h, baerAdd_def m h f]
  simp only [mul_assoc]
  rw [(commute_of_mem_center (Subgroup.pow_mem _ (hcen h g) m) f).left_comm,
    (commute_of_mem_center (Subgroup.pow_mem _ (hcen f h) m) (⁅h, g⁆ ^ m * ⁅f, g⁆ ^ m)).eq,
    mul_assoc]

theorem baerAdd_comm (m : ℕ) (hhalf : ∀ x : H, x ^ (2 * m) = x)
    (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H) (g h : H) :
    baerAdd m g h = baerAdd m h g := by
  have hgh : g * h = h * g * ⁅g, h⁆ := by
    rw [Subgroup.mem_center_iff.mp (hcen g h) (h * g), commutatorElement_def]
    group
  have hsq : ⁅g, h⁆ = ⁅g, h⁆ ^ m * ⁅g, h⁆ ^ m := by
    rw [← pow_add, ← two_mul, hhalf]
  rw [baerAdd_def, baerAdd_def, ← commutatorElement_inv g h, inv_pow, hgh, mul_assoc (h * g),
    mul_inv_eq_iff_eq_mul.mpr hsq]

theorem baerAdd_one_left (m : ℕ) (g : H) : baerAdd m 1 g = g := by
  rw [baerAdd_def, commutatorElement_one_right, one_pow, mul_one, one_mul]

theorem baerAdd_inv_left (m : ℕ) (g : H) : baerAdd m g⁻¹ g = 1 := by
  have hg : ⁅g, g⁻¹⁆ = 1 := by
    rw [commutatorElement_def]
    group
  rw [baerAdd_def, hg, one_pow, inv_mul_cancel, mul_one]

theorem map_baerAdd (m : ℕ) (f : H →* H) (g h : H) :
    f (baerAdd m g h) = baerAdd m (f g) (f h) := by
  simp only [baerAdd_def, map_mul, map_pow, map_commutatorElement]

@[instance_reducible]
def baerAddCommGroup (m : ℕ) (hhalf : ∀ x : H, x ^ (2 * m) = x)
    (hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H) : AddCommGroup H :=
  letI : Add H := ⟨baerAdd m⟩
  letI : Zero H := ⟨1⟩
  letI : Neg H := ⟨fun g => g⁻¹⟩
  { AddGroup.ofLeftAxioms (baerAdd_assoc m hcen) (baerAdd_one_left m) (baerAdd_inv_left m) with
    add_comm := baerAdd_comm m hhalf hcen }

end Baer

theorem exists_baer_addCommGroup {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    (hcomm : ∀ x y z : H, ⁅x, y⁆ * z = z * ⁅x, y⁆) :
    ∃ _ : AddCommGroup H, ∀ (f : H →* H) (g h : H), f (g + h) = f g + f h := by
  obtain ⟨k, hk⟩ := hodd
  have hhalf : ∀ x : H, x ^ (2 * (k + 1)) = x := fun x => by
    rw [show 2 * (k + 1) = Nat.card H + 1 by omega, pow_succ, pow_card_eq_one', one_mul]
  have hcen : ∀ x y : H, ⁅x, y⁆ ∈ Subgroup.center H := fun x y =>
    Subgroup.mem_center_iff.mpr fun g => (hcomm x y g).symm
  exact ⟨Baer.baerAddCommGroup (k + 1) hhalf hcen, fun f g h => Baer.map_baerAdd (k + 1) f g h⟩

end CFSG.SignalizerFunctorTheorem.MinimalAction
