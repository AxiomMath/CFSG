
module

public import Certificates.Data.CFSGNative.MonsterB.Short
public import CFSG.Monster.B.Short.AxisOrbit
public import CFSG.Monster.VisCert.Delta
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

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.Generated

def wStar (i : ℕ) : ℤ := if i = 0 then 4 else if i = 1 then -4 else 0

theorem wStar_apply : ∀ i : Fin 24, wStar i = vMinus 0 1 i := by decide +kernel

theorem wStar_eq : (fun i : Fin 24 => wStar i) = vMinus 0 1 := funext wStar_apply

theorem rowCheck_wStar : rowCheck wStar Native.shortSeed = true := by decide +kernel

theorem dec_shortSeed : dec Native.shortSeed = classOf (vMinus 0 1) := by
  have hw : (fun i : Fin 24 => wStar i) ∈ codeLattice C := wStar_eq ▸ vMinus_zero_one_mem.1
  rw [← cls_eq_dec_of_rowCheck hw rowCheck_wStar, classOf_eq_cls vMinus_zero_one_mem.1]
  exact cls_congr hw wStar_eq

theorem classOf_vMinus_mem_shortSet : classOf (vMinus 0 1) ∈ shortSet :=
  ⟨_, vMinus_zero_one_mem, rfl⟩

theorem phi0_mem_shortSet {r : Q} (hr : IsShortCoord (coordOf r)) : phi0 (coordOf r) ∈ shortSet :=
  hr

theorem smul_mem_shortSet_of_mem_Hvis {u : GLV} (hu : u ∈ Hvis) {x : L2} (hx : x ∈ shortSet) :
    u • x ∈ shortSet := by
  obtain ⟨g, -, rfl⟩ := mem_Hvis.1 hu
  exact modTwoEnd_mem_shortSet g hx

end CFSG.Monster.B.Short
