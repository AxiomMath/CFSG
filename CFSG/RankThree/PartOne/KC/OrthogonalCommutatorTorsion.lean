module

public import CFSG.RankThree.PartOne.KC.MatrixAlgebraFieldProduct
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

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial

variable {K : Type*} [Field K]

@[expose] noncomputable def adjoinRootMap (σ : K ≃+* K) (h : K[X])
    (hσ : h.map (σ : K →+* K) = h) : AdjoinRoot h →+* AdjoinRoot h :=
  AdjoinRoot.lift ((algebraMap K (AdjoinRoot h)).comp (σ : K →+* K)) (AdjoinRoot.root h) (by
    rw [← Polynomial.eval₂_map, hσ]
    exact AdjoinRoot.eval₂_root h)

theorem adjoinRootMap_mk (σ : K ≃+* K) (h : K[X]) (hσ : h.map (σ : K →+* K) = h) (f : K[X]) :
    adjoinRootMap σ h hσ (AdjoinRoot.mk h f) = AdjoinRoot.mk h (f.map (σ : K →+* K)) := by
  rw [adjoinRootMap, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq]
  rfl

theorem map_ringEquiv_one (f : K[X]) : f.map (((1 : K ≃+* K) : K ≃+* K) : K →+* K) = f := by
  have : (((1 : K ≃+* K) : K ≃+* K) : K →+* K) = RingHom.id K := rfl
  rw [this, Polynomial.map_id]

theorem adjoinRootMap_iterate (σ : K ≃+* K) (h : K[X]) (hσ : h.map (σ : K →+* K) = h) (n : ℕ)
    (f : K[X]) :
    (adjoinRootMap σ h hσ)^[n] (AdjoinRoot.mk h f) =
      AdjoinRoot.mk h (f.map ((σ ^ n : K ≃+* K) : K →+* K)) := by
  induction n with
  | zero => simp [map_ringEquiv_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, adjoinRootMap_mk, Polynomial.map_map, pow_succ']
    rfl

theorem mk_map_eq_of_pow_two_pow_eq_one {σ : K ≃+* K} {N : ℕ} (hN : Odd N) (hσN : σ ^ N = 1)
    {h : K[X]} [Fact (Irreducible h)] (hσ : h.map (σ : K →+* K) = h) {f : K[X]} {s : ℕ}
    (hf : AdjoinRoot.mk h f ^ 2 ^ s = 1) :
    AdjoinRoot.mk h (f.map (σ : K →+* K)) = AdjoinRoot.mk h f := by
  have hτ : ∀ y : AdjoinRoot h, (adjoinRootMap σ h hσ).toMonoidHom^[N] y = y := by
    intro y
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
    change (adjoinRootMap σ h hσ)^[N] (AdjoinRoot.mk h g) = AdjoinRoot.mk h g
    rw [adjoinRootMap_iterate, hσN, map_ringEquiv_one]
  have := KCMatrixAlgebra.monoidHom_apply_eq_of_pow_two_pow_eq_one
    (adjoinRootMap σ h hσ).toMonoidHom hN hτ hf
  rwa [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, adjoinRootMap_mk] at this

end CFSG.RankThree.PartOne.KCOrthComm
