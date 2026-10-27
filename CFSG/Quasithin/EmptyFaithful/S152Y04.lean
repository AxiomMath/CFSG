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

namespace CFSG.Quasithin

open scoped commutatorElement

variable {A : Type*} [Group A]

@[expose, instance_reducible] def commGroupOfComm (D : Subgroup A)
    (h : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) : CommGroup ↥D :=
  { (inferInstance : Group ↥D) with mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

theorem pow_card_eq_one_of_mem_commutator {D R : Subgroup A} [Finite R]
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hRD : R ≤ Subgroup.normalizer (D : Set A))
    {k : A} (hk : k ∈ ⁅D, R⁆) (hkR : ∀ ρ ∈ R, ρ * k * ρ⁻¹ = k) : k ^ Nat.card R = 1 := by
  classical
  let _ : CommGroup ↥D := commGroupOfComm D hD
  have _ : Fintype R := Fintype.ofFinite R
  let c : R → ↥D → ↥D := fun ρ d =>
    ⟨(ρ : A) * d * (ρ : A)⁻¹, (Subgroup.mem_normalizer_iff.mp (hRD ρ.2) d).mp d.2⟩
  have c_val : ∀ ρ (d : ↥D), ((c ρ d : ↥D) : A) = (ρ : A) * d * (ρ : A)⁻¹ := fun _ _ => rfl
  have c_mul : ∀ ρ (a b : ↥D), c ρ (a * b) = c ρ a * c ρ b := by
    intro ρ a b
    apply Subtype.ext
    simp only [c_val, Subgroup.coe_mul]
    group
  have c_inv : ∀ ρ (a : ↥D), c ρ a⁻¹ = (c ρ a)⁻¹ := by
    intro ρ a
    apply Subtype.ext
    simp only [c_val, Subgroup.coe_inv]
    group
  have c_c : ∀ ρ σ (a : ↥D), c ρ (c σ a) = c (ρ * σ) a := by
    intro ρ σ a
    apply Subtype.ext
    simp only [c_val, Subgroup.coe_mul]
    group
  have c_one : ∀ ρ, c ρ 1 = 1 := by
    intro ρ
    apply Subtype.ext
    show (ρ : A) * 1 * (ρ : A)⁻¹ = 1
    group
  let nm : ↥D → ↥D := fun a => ∏ ρ : R, c ρ a
  have nm_mul : ∀ a b, nm (a * b) = nm a * nm b := by
    intro a b
    simp only [nm, c_mul]
    exact Finset.prod_mul_distrib
  have nm_inv : ∀ a, nm a⁻¹ = (nm a)⁻¹ := by
    intro a
    simp only [nm, c_inv]
    exact Finset.prod_inv_distrib (f := fun ρ : R => c ρ a)
  have nm_c : ∀ σ a, nm (c σ a) = nm a := by
    intro σ a
    simp only [nm, c_c]
    exact Fintype.prod_equiv (Equiv.mulRight σ) _ _ (fun ρ => rfl)
  have hker : ∀ x ∈ ⁅D, R⁆, ∃ hx : x ∈ D, nm ⟨x, hx⟩ = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨d, hd, ρ, hρ, rfl⟩ := hx
      have hmem : ⁅d, ρ⁆ ∈ D := by
        have := D.mul_mem hd (D.inv_mem ((Subgroup.mem_normalizer_iff.mp (hRD hρ) d).mp hd))
        have e : ⁅d, ρ⁆ = d * (ρ * d * ρ⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
        rw [e]
        exact this
      refine ⟨hmem, ?_⟩
      have e : (⟨⁅d, ρ⁆, hmem⟩ : ↥D) = ⟨d, hd⟩ * (c ⟨ρ, hρ⟩ ⟨d, hd⟩)⁻¹ := by
        apply Subtype.ext
        simp only [c_val, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e, nm_mul, nm_inv, nm_c]
      exact mul_inv_cancel _
    | one =>
      refine ⟨D.one_mem, ?_⟩
      show nm 1 = 1
      simp only [nm, c_one]
      exact Finset.prod_const_one
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, hx1⟩ := ihx
      obtain ⟨hy, hy1⟩ := ihy
      refine ⟨D.mul_mem hx hy, ?_⟩
      have : (⟨x * y, D.mul_mem hx hy⟩ : ↥D) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, nm_mul, hx1, hy1]
      exact mul_one _
    | inv x _ ih =>
      obtain ⟨hx, hx1⟩ := ih
      refine ⟨D.inv_mem hx, ?_⟩
      have : (⟨x⁻¹, D.inv_mem hx⟩ : ↥D) = (⟨x, hx⟩ : ↥D)⁻¹ := rfl
      rw [this, nm_inv, hx1]
      exact inv_one
  obtain ⟨hkD, hk1⟩ := hker k hk
  have hfix : ∀ ρ : R, c ρ ⟨k, hkD⟩ = ⟨k, hkD⟩ := fun ρ => Subtype.ext (hkR ρ ρ.2)
  have : nm ⟨k, hkD⟩ = (⟨k, hkD⟩ : ↥D) ^ Nat.card R := by
    simp only [nm, hfix, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [this] at hk1
  have := congrArg (fun z : ↥D => (z : A)) hk1
  simpa using this

end CFSG.Quasithin
