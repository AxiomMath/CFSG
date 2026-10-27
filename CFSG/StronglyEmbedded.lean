module

public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace CFSG

open Matrix
namespace BenderSuzuki

universe u

theorem bender_suzuki {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    CFSG.BenderSuzuki.IsBenderGroup X := by
  have hB : BenderSuzuki.IsSimpleBenderGroup X :=
    _root_.CFSG.BenderSuzuki.theorem_SE_simple M
      (isStronglyEmbedded_of_parity M h)
      (inferInstance : IsSimpleGroup X)
  rcases hB with
    ⟨⟨n, hn, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, E, hEfield, hEfinite, J, hform, hEcard, hfixed, ⟨e⟩⟩⟩
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSL2 n hn e
  · exact CFSG.BenderSuzuki.IsBenderGroup.isSuzuki n hn
      (e.trans (MulEquiv.subgroupCongr
        (szModel_eq_suzukiMatrixGroup n).symm))
  · let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨u⟩ := projectiveSpecialUnitary_equiv_PSU3Model
      J n hn hform hEcard hfixed
    exact CFSG.BenderSuzuki.IsBenderGroup.isPSU3 n hn (e.trans u)

end BenderSuzuki

end CFSG
