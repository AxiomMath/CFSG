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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

namespace CFSG.Open.StatedAPI

theorem card_mulVec_fixed_le {K : Type} [Field K] [Finite K] {M : Matrix (Fin 2) (Fin 2) K}
    (hM1 : M ≠ 1) : Nat.card {v : Fin 2 → K // M.mulVec v = v} ≤ Nat.card K := by
  let f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := Matrix.mulVecLin (M - 1)
  have hne : LinearMap.ker f ≠ ⊤ := by
    intro htop
    apply hM1
    have h0 : ∀ v : Fin 2 → K, (M - 1).mulVec v = 0 := fun v => by
      have hv : v ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
      exact LinearMap.mem_ker.mp hv
    have h1 : M - 1 = 0 :=
      Matrix.ext_of_mulVec_single (fun i => by rw [h0, Matrix.zero_mulVec])
    exact sub_eq_zero.mp h1
  have hlt : Module.finrank K (LinearMap.ker f) < Module.finrank K (Fin 2 → K) :=
    Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at hlt
  have hcard : Nat.card (LinearMap.ker f) ≤ Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K)]
    calc Nat.card K ^ Module.finrank K (LinearMap.ker f) ≤ Nat.card K ^ 1 :=
          Nat.pow_le_pow_right Nat.card_pos (by omega)
      _ = Nat.card K := pow_one _
  have hmem : ∀ v : {v : Fin 2 → K // M.mulVec v = v}, v.1 ∈ LinearMap.ker f := by
    intro v
    rw [LinearMap.mem_ker]
    show (M - 1).mulVec _ = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    exact v.2
  refine le_trans (Nat.card_le_card_of_injective
    (fun v => (⟨v.1, hmem v⟩ : LinearMap.ker f)) ?_) hcard
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : ↥(LinearMap.ker f) => (z : Fin 2 → K)) hxy)

end CFSG.Open.StatedAPI
