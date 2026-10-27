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

open scoped commutatorElement

namespace CFSG.Quasithin.H11Proof

@[expose] def linToMulAut (F W : Type*) [Field F] [AddCommGroup W] [Module F W] :
    (W ≃ₗ[F] W) →* MulAut (Multiplicative W) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def IsFTransvection (F : Type*) [Field F] (ι : Type*) [Fintype ι]
    (t : MulAut (Multiplicative (ι → F))) : Prop :=
  ∃ g : (ι → F) ≃ₗ[F] (ι → F), linToMulAut F (ι → F) g = t ∧
    Module.finrank F (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1 ∧
    (g.toLinearMap - LinearMap.id) ∘ₗ (g.toLinearMap - LinearMap.id) = 0

section Orth

variable (F : Type*) [Field F]

@[expose] def orthPlus (x : Fin 4 → F) : F := x 0 * x 1 + x 2 * x 3

@[expose] def orthMinus (a : F) (x : Fin 4 → F) : F :=
  x 0 * x 1 + x 2 ^ 2 + x 2 * x 3 + a * x 3 ^ 2

@[expose] def isometryGroup (Q : (Fin 4 → F) → F) : Subgroup ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  mul_mem' {g h} hg hh x := by
    show Q (g (h x)) = Q x
    rw [hg, hh]
  one_mem' _ := rfl
  inv_mem' {g} hg x := by
    show Q (g.symm x) = Q x
    have := hg (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

@[expose] def omegaFour (Q : (Fin 4 → F) → F) : Subgroup (MulAut (Multiplicative (Fin 4 → F))) :=
  (⁅isometryGroup F Q, isometryGroup F Q⁆).map (linToMulAut F (Fin 4 → F))

end Orth

@[expose] def IsOrthOmega (F : Type*) [Field F] (ε : ℤ) {V : Type*} [CommGroup V]
    (e : V ≃* Multiplicative (Fin 4 → F)) (L : Subgroup (MulAut V)) : Prop :=
  (ε = 1 ∧ L.map (MulAut.congr e).toMonoidHom = omegaFour F (orthPlus F)) ∨
  (ε = -1 ∧ ∃ a : F, (∀ t : F, t ^ 2 + t + a ≠ 0) ∧
    L.map (MulAut.congr e).toMonoidHom = omegaFour F (orthMinus F a))

end CFSG.Quasithin.H11Proof
