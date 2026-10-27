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
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
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
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public noncomputable section

namespace CFSG.Quasithin

namespace B5FinWedge

open Matrix

@[expose] def pr4 : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

variable {K : Type*} [Field K]

@[expose] def minorAlt4 (i j : Fin 4) : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] K :=
  (Matrix.detRowAlternating : (Fin 2 → K) [⋀^Fin 2]→ₗ[K] K).compLinearMap
    (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j])

theorem minorAlt4_apply (i j : Fin 4) (v : Fin 2 → Fin 4 → K) :
    minorAlt4 i j v = v 0 i * v 1 j - v 0 j * v 1 i := by
  change Matrix.det (Matrix.of fun a => (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j] :
    (Fin 4 → K) →ₗ[K] (Fin 2 → K)) (v a)) = _
  rw [det_fin_two]
  simp

@[expose] def wedgeCoord4 : ⋀[K]^2 (Fin 4 → K) →ₗ[K] (Fin 6 → K) :=
  LinearMap.pi fun k => exteriorPower.alternatingMapLinearEquiv (minorAlt4 (pr4 k).1 (pr4 k).2)

theorem wedgeCoord4_ιMulti (v : Fin 2 → Fin 4 → K) (k : Fin 6) :
    wedgeCoord4 (exteriorPower.ιMulti K 2 v) k =
      v 0 (pr4 k).1 * v 1 (pr4 k).2 - v 0 (pr4 k).2 * v 1 (pr4 k).1 := by
  rw [wedgeCoord4, LinearMap.pi_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    minorAlt4_apply]

@[expose] def wedgeMat4 (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun k l => g (pr4 k).1 (pr4 l).1 * g (pr4 k).2 (pr4 l).2 -
    g (pr4 k).1 (pr4 l).2 * g (pr4 k).2 (pr4 l).1

theorem wedgeCoord4_map (g : Matrix (Fin 4) (Fin 4) K) (x : ⋀[K]^2 (Fin 4 → K)) :
    wedgeCoord4 (exteriorPower.map 2 (Matrix.toLin' g) x) = wedgeMat4 g *ᵥ wedgeCoord4 x := by
  have h : wedgeCoord4 ∘ₗ exteriorPower.map 2 (Matrix.toLin' g) =
      (wedgeMat4 g).mulVecLin ∘ₗ wedgeCoord4 := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    funext k
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, Matrix.mulVecLin_apply]
    rw [wedgeCoord4_ιMulti]
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, wedgeCoord4_ιMulti,
      Function.comp_apply, Matrix.toLin'_apply]
    fin_cases k <;> simp [wedgeMat4, pr4] <;> ring
  exact LinearMap.congr_fun h x

@[expose] def wedgeBasis4 (k : Fin 6) : ⋀[K]^2 (Fin 4 → K) :=
  exteriorPower.ιMulti K 2 ![Pi.single (pr4 k).1 1, Pi.single (pr4 k).2 1]

theorem wedgeCoord4_basis (k : Fin 6) :
    wedgeCoord4 (wedgeBasis4 k : ⋀[K]^2 (Fin 4 → K)) = Pi.single k 1 := by
  funext l
  rw [wedgeBasis4, wedgeCoord4_ιMulti]
  fin_cases k <;> fin_cases l <;> simp [pr4]

theorem wedgeCoord4_surjective : Function.Surjective (wedgeCoord4 (K := K)) := by
  intro c
  refine ⟨∑ k, c k • wedgeBasis4 k, ?_⟩
  rw [map_sum]
  simp only [map_smul, wedgeCoord4_basis]
  funext l
  simp [Finset.sum_apply, Pi.single_apply]

theorem finrank_wedge4 : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = 6 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
  rfl

theorem wedgeCoord4_bijective : Function.Bijective (wedgeCoord4 (K := K)) := by
  have h : Module.finrank K (⋀[K]^2 (Fin 4 → K)) = Module.finrank K (Fin 6 → K) := by
    rw [finrank_wedge4, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mpr wedgeCoord4_surjective,
    wedgeCoord4_surjective⟩

variable (K) in
@[expose] def wedgeEquiv4 : ⋀[K]^2 (Fin 4 → K) ≃ₗ[K] (Fin 6 → K) :=
  LinearEquiv.ofBijective wedgeCoord4 wedgeCoord4_bijective

theorem wedgeEquiv4_apply (x : ⋀[K]^2 (Fin 4 → K)) : wedgeEquiv4 K x = wedgeCoord4 x :=
  rfl

end B5FinWedge

end CFSG.Quasithin
