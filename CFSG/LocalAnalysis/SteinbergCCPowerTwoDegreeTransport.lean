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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
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

namespace CFSG.LocalAnalysis

open Matrix

namespace PowerTwoDegree

@[expose] noncomputable def slMapEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SpecialLinearGroup (Fin 2) R ≃* SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map (e : R →+* S)
  invFun := Matrix.SpecialLinearGroup.map (e.symm : S →+* R)
  left_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

theorem map_center_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map (e : G →* H) = Subgroup.center H := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hg
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    change e x * e g = e g * e x
    rw [← map_mul, ← map_mul, hg x]
  · intro hh
    refine ⟨e.symm h, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hh
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hh (e x)]

@[expose] noncomputable def pslMapEquiv {E F : Type*} [Field E] [Field F] (e : E ≃+* F) :
    ProjectiveSpecialLinearGroup (Fin 2) E ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.congr _ _ (slMapEquiv e) (map_center_eq (slMapEquiv e))

end PowerTwoDegree

section PrimeField

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end PrimeField

end CFSG.LocalAnalysis
