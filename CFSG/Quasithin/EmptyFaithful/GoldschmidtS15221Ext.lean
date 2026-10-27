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

namespace CFSG.Quasithin.S15221

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem commutator_mul_central {X Z : Subgroup Γ} (hZX : Z ≤ X)
    (hZ : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hc : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z)
    {a b z w : Γ} (ha : a ∈ X) (hb : b ∈ X) (hz : z ∈ Z) (hw : w ∈ Z) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hwb : w * b ∈ X := X.mul_mem (hZX hw) hb
  have h1 : ⁅z * a, w * b⁆ = ⁅a, w * b⁆ := by
    have hk : ⁅a, w * b⁆ ∈ Z := hc a ha _ hwb
    have e1 : z * ⁅a, w * b⁆ * z⁻¹ = ⁅a, w * b⁆ := by
      rw [hZ z hz _ (hZX hk)]
      group
    have e2 : ⁅z, w * b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZ z hz _ hwb)
    rw [commutatorElement_mul_left_eq_conj_mul, e1, e2, mul_one]
  rw [h1, commutatorElement_mul_right_eq_mul_conj]
  have hk : ⁅a, b⁆ ∈ Z := hc a ha b hb
  have e3 : ⁅a, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZ w hw a ha).symm
  have e4 : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := by
    rw [hZ w hw _ (hZX hk)]
    group
  rw [e3, one_mul, e4]

theorem commutator_inv_inv {X Z : Subgroup Γ} (hZ : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z)
    (hc : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z) {a b : Γ} (ha : a ∈ X) (hb : b ∈ X) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have hk : ⁅a, b⁆ ∈ Z := hc a ha b hb
  have hab : a * b = ⁅a, b⁆ * (b * a) := by
    simp only [commutatorElement_def]
    group
  have hkb : b⁻¹ * ⁅a, b⁆ = ⁅a, b⁆ * b⁻¹ := (hZ _ hk b⁻¹ (X.inv_mem hb)).symm
  have hka : a⁻¹ * ⁅a, b⁆ = ⁅a, b⁆ * a⁻¹ := (hZ _ hk a⁻¹ (X.inv_mem ha)).symm
  calc ⁅a⁻¹, b⁻¹⁆ = a⁻¹ * b⁻¹ * (a * b) := by simp only [commutatorElement_def]; group
    _ = a⁻¹ * b⁻¹ * (⁅a, b⁆ * (b * a)) := by rw [← hab]
    _ = a⁻¹ * (b⁻¹ * ⁅a, b⁆) * (b * a) := by group
    _ = (a⁻¹ * ⁅a, b⁆) * a := by rw [hkb]; group
    _ = ⁅a, b⁆ := by rw [hka]; group

theorem conj_commutator_eq {X Z : Subgroup Γ} (hZX : Z ≤ X)
    (hZ : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hc : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z) {g : Γ}
    (hsc : (∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Z) ∨ (∀ x ∈ X, g * x * g⁻¹ * x ∈ Z)) {a b : Γ}
    (ha : a ∈ X) (hb : b ∈ X) : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
  rw [conjugate_commutatorElement]
  rcases hsc with h | h
  · calc ⁅g * a * g⁻¹, g * b * g⁻¹⁆
        = ⁅(g * a * g⁻¹ * a⁻¹) * a, (g * b * g⁻¹ * b⁻¹) * b⁆ := by
          congr 1 <;> group
      _ = ⁅a, b⁆ := commutator_mul_central hZX hZ hc ha hb (h a ha) (h b hb)
  · calc ⁅g * a * g⁻¹, g * b * g⁻¹⁆
        = ⁅(g * a * g⁻¹ * a) * a⁻¹, (g * b * g⁻¹ * b) * b⁻¹⁆ := by
          congr 1 <;> group
      _ = ⁅a⁻¹, b⁻¹⁆ := commutator_mul_central hZX hZ hc (X.inv_mem ha) (X.inv_mem hb)
          (h a ha) (h b hb)
      _ = ⁅a, b⁆ := commutator_inv_inv hZ hc ha hb

theorem conj_eq_of_mem_commutator {X Z : Subgroup Γ} (hZX : Z ≤ X)
    (hZ : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (hc : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ Z) {g : Γ}
    (hsc : (∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Z) ∨ (∀ x ∈ X, g * x * g⁻¹ * x ∈ Z)) {z : Γ}
    (hz : z ∈ ⁅X, X⁆) : g * z * g⁻¹ = z := by
  rw [Subgroup.commutator_def] at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact conj_commutator_eq hZX hZ hc hsc ha hb
  | one => simp
  | mul x y _ _ hx hy =>
    calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      _ = x * y := by rw [hx, hy]
  | inv x _ hx =>
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hx]

end CFSG.Quasithin.S15221
