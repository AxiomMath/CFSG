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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

open Module
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

@[expose] def conjHom {X Γ : Type*} [Group X] [Group Γ] (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) : Γ →* MulAut V where
  toFun g :=
    { toFun := fun v => ⟨φ g * v * (φ g)⁻¹, hnorm g v v.2⟩
      invFun := fun v => ⟨(φ g)⁻¹ * v * φ g, by
        have := hnorm g⁻¹ v v.2
        simpa [map_inv] using this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [mul_assoc]

theorem conjHom_apply {X Γ : Type*} [Group X] [Group Γ] (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (v : V) :
    ((conjHom φ V hnorm g v : V) : X) = φ g * v * (φ g)⁻¹ := rfl

variable {X Γ : Type*} [Group X] [Group Γ]

theorem exists_rep_of_elementary_abelian (φ : Γ →* X) (V : Subgroup X) [Finite V]
    [IsMulCommutative V] {s : ℕ} (hs : s.Prime) (hexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (F : Type*) [Field F] [CharP F s] :
    ∃ (m : ℕ) (ρ : Γ →* Module.End F (Fin m → F)), Nat.card V = s ^ m ∧
      ∀ g, ρ g = 1 → ∀ v ∈ V, φ g * v * (φ g)⁻¹ = v := by
  have : Fact s.Prime := ⟨hs⟩
  let _ : Algebra (ZMod s) F := ZMod.algebra F s
  have hmod : Module (ZMod s) (Additive V) :=
    AddCommGroup.zmodModule (n := s) (fun x => by
      show s • x = 0
      apply Additive.toMul.injective
      simp only [toMul_nsmul, toMul_zero]
      exact Subtype.ext (hexp _ x.toMul.2))
  have : Module.Finite (ZMod s) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod s) (Additive V)
  let m := finrank (ZMod s) (Additive V)
  let T : Γ →* Module.End (ZMod s) (Additive V) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap s
        (AddMonoidHom.mk' (fun x : Additive V => Additive.ofMul (conjHom φ V hnorm g x.toMul))
          (fun x y => by simp))
      map_one' := by
        ext x
        simp [AddMonoidHom.toZModLinearMap]
      map_mul' := fun a b => by
        ext x
        simp [AddMonoidHom.toZModLinearMap] }
  let Φ : Module.End (ZMod s) (Additive V) →* Module.End F (Fin m → F) :=
    (((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).toAlgHom.toRingHom).comp
      ((algebraMap (ZMod s) F).mapMatrix.comp
        (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom) :
        Module.End (ZMod s) (Additive V) →+* Module.End F (Fin m → F))
  have hΦ : Function.Injective Φ := by
    intro f g h
    have h1 := (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).injective h
    have h2 : (LinearMap.toMatrixAlgEquiv b f) = (LinearMap.toMatrixAlgEquiv b g) :=
      Matrix.map_injective (algebraMap (ZMod s) F).injective h1
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  refine ⟨m, Φ.comp T, ?_, ?_⟩
  · have h1 : Nat.card (Additive V) = s ^ m := by
      have := Fintype.ofFinite (Additive V)
      have := Module.card_eq_pow_finrank (K := ZMod s) (V := Additive V)
      rw [Nat.card_eq_fintype_card, this, ZMod.card]
    rw [← h1]
    exact (Nat.card_congr Additive.toMul).symm
  · intro g hg v hv
    have h1 : T g = 1 := hΦ (by rw [MonoidHom.comp_apply] at hg; rw [hg, map_one])
    have h2 := LinearMap.congr_fun h1 (Additive.ofMul ⟨v, hv⟩)
    have h3 := congrArg (fun x : Additive V => (x.toMul : X)) h2
    simpa [T, AddMonoidHom.toZModLinearMap, conjHom_apply] using h3

end CFSG.SignalizerFunctorTheorem.NonLocal
