module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.Monster.B.Generic

theorem locally_coconnected_graph_complement_connected {V : Type*} [Nonempty V]
    (X : SimpleGraph V) (hedge : ∀ x, (X.induce (X.neighborSet x)).edgeSet.Nonempty)
    (hco : ∀ x, (X.induce (X.neighborSet x))ᶜ.Connected) : Xᶜ.Connected := by
  refine (SimpleGraph.connected_iff _).mpr ⟨fun u v => ?_, inferInstance⟩
  by_contra huv
  have hcross : ∀ a b, Xᶜ.Reachable u a → ¬ Xᶜ.Reachable u b → X.Adj a b := by
    intro a b ha hb
    by_contra hab
    have hne : a ≠ b := fun h => hb (h ▸ ha)
    exact hb (ha.trans (SimpleGraph.Adj.reachable (by simp [SimpleGraph.compl_adj, hne, hab])))
  have hsplit : ∀ y p q, X.Adj y p → X.Adj y q → Xᶜ.Reachable u p → ¬ Xᶜ.Reachable u q →
      False := by
    intro y p q hp hq hpA hqA
    obtain ⟨w⟩ := (hco y).preconnected ⟨p, hp⟩ ⟨q, hq⟩
    obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart {z | Xᶜ.Reachable u z.1} hpA hqA
    have hd := d.adj
    rw [SimpleGraph.compl_adj] at hd
    exact hd.2 (by simpa using hcross _ _ hd1 hd2)
  have hv : X.Adj u v := hcross u v (SimpleGraph.Reachable.refl u) huv
  have hout : ∀ y, X.Adj u y → ¬ Xᶜ.Reachable u y := fun y hy hyA =>
    hsplit u y v hy hv hyA huv
  obtain ⟨e, he⟩ := hedge u
  induction e using Sym2.ind with
  | h y z =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact hsplit y u z (X.adj_symm y.2) (by simpa using he) (SimpleGraph.Reachable.refl u)
      (hout z z.2)

end CFSG.Monster.B.Generic
