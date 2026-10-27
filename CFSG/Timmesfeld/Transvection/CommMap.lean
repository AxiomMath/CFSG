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

namespace CFSG.Timmesfeld.Transvection

variable {G : Type*} [Group G] {C : Subgroup G} {h : G}

@[expose] def commMap (hC : ∀ x ∈ C, ∀ y ∈ C, Commute x y) (hh : ∀ x ∈ C, h * x * h⁻¹ ∈ C) :
    C →* C where
  toFun m := ⟨m * h * (m : G)⁻¹ * h⁻¹, by
    have h1 : (m : G) * h * (m : G)⁻¹ * h⁻¹ = m * (h * (m : G) * h⁻¹)⁻¹ := by group
    rw [h1]
    exact C.mul_mem m.2 (C.inv_mem (hh _ m.2))⟩
  map_one' := by
    ext
    simp
  map_mul' m m' := by
    ext
    have hc : Commute (m' : G) (h * (m : G)⁻¹ * h⁻¹) :=
      hC _ m'.2 _ (by
        have := hh _ (C.inv_mem m.2)
        simpa [mul_assoc] using this)
    have hmm : (m : G)⁻¹ * (m' : G)⁻¹ = (m' : G)⁻¹ * (m : G)⁻¹ :=
      (hC _ m.2 _ m'.2).inv_inv.eq
    show (m : G) * m' * h * ((m : G) * m')⁻¹ * h⁻¹ =
      (m : G) * h * (m : G)⁻¹ * h⁻¹ * ((m' : G) * h * (m' : G)⁻¹ * h⁻¹)
    symm
    calc (m : G) * h * (m : G)⁻¹ * h⁻¹ * ((m' : G) * h * (m' : G)⁻¹ * h⁻¹) =
        (m : G) * ((h * (m : G)⁻¹ * h⁻¹) * m') * (h * (m' : G)⁻¹ * h⁻¹) := by group
      _ = (m : G) * (m' * (h * (m : G)⁻¹ * h⁻¹)) * (h * (m' : G)⁻¹ * h⁻¹) := by rw [hc.eq]
      _ = (m : G) * m' * h * ((m : G)⁻¹ * (m' : G)⁻¹) * h⁻¹ := by group
      _ = (m : G) * m' * h * ((m' : G)⁻¹ * (m : G)⁻¹) * h⁻¹ := by rw [hmm]
      _ = (m : G) * m' * h * ((m : G) * m')⁻¹ * h⁻¹ := by group

variable (hC : ∀ x ∈ C, ∀ y ∈ C, Commute x y) (hh : ∀ x ∈ C, h * x * h⁻¹ ∈ C)

@[simp] theorem coe_commMap (m : C) :
    (commMap hC hh m : G) = m * h * (m : G)⁻¹ * h⁻¹ := rfl

theorem mem_ker_commMap_iff (m : C) : m ∈ (commMap hC hh).ker ↔ Commute (m : G) h := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_commMap, Subgroup.coe_one]
  constructor
  · intro h1
    have : (m : G) * h = h * m := by
      calc (m : G) * h = (m : G) * h * (m : G)⁻¹ * h⁻¹ * (h * m) := by group
        _ = h * m := by rw [h1, one_mul]
    exact this
  · intro h1
    rw [h1.eq]
    group

theorem card_range_commMap_mul [Finite G] :
    Nat.card (commMap hC hh).range * Nat.card (commMap hC hh).ker = Nat.card C := by
  rw [← Subgroup.card_mul_index (commMap hC hh).ker, mul_comm]
  congr 1
  rw [Subgroup.index]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (commMap hC hh)).toEquiv).symm

end CFSG.Timmesfeld.Transvection
