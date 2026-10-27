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

namespace CFSG.StandardType

variable {G : Type*} [Group G]

theorem exists_inner_of_mem_normalizer {L : Subgroup G}
    (hAut : ∀ φ : MulAut ↥L, ∃ l : ↥L, φ = MulAut.conj l) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l ∈ L, ∀ y ∈ L, g * y * g⁻¹ = l * y * l⁻¹ := by
  have hmap : L.map (MulAut.conj g) = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let φ : MulAut ↥L := ((MulAut.conj g).subgroupMap L).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨l, hl⟩ := hAut φ
  refine ⟨l, l.2, fun y hy => ?_⟩
  have h := congrArg (fun z : ↥L => (z : G)) (DFunLike.congr_fun hl ⟨y, hy⟩)
  simpa [φ, MulAut.conj_apply] using h

end CFSG.StandardType
