module

public import CFSG.ClassicalGroups.Orthogonal.Basic
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem exists_nonsingular_perp {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K V) {u : V} (hu0 : u ≠ 0) :
    ∃ w : V, polar Q u w = 0 ∧ Q w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hPdef⟩ : ∃ P : Submodule K V,
      P = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := ⟨_, rfl⟩
  have hPu : ∀ w ∈ P, polar Q u w = 0 := by
    intro w hw
    rw [hPdef, LinearMap.BilinForm.mem_orthogonal_iff] at hw
    exact hw u (Submodule.mem_span_singleton_self u)
  have hPQ : ∀ w ∈ P, Q w = 0 := fun w hw => hcon w (hPu w hw)
  have hPle : P ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) P := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    show polar Q n a = 0
    have h1 := hPQ _ (P.add_mem hn ha)
    have h2 := hPQ n hn
    have h3 := hPQ a ha
    show Q (n + a) - Q n - Q a = 0
    linear_combination h1 - h2 - h3
  have hfinP : Module.finrank K P = Module.finrank K V - 1 := by
    rw [hPdef, LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hu0]
  have hfinPperp := LinearMap.BilinForm.finrank_orthogonal hQ P
  have hmono := Submodule.finrank_mono hPle
  omega

end CFSG.RankThree.GF2n.Stroth80
