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

namespace CFSG.Quasithin

theorem exists_coord_of_mulAut {G A : Type} [Group G] [CommGroup A] [Finite A] {d : ℕ}
    (hA : ∀ a : A, a ^ 2 = 1) (hd : Nat.card A = 2 ^ d) (φ : G →* MulAut A) :
    ∃ (β : A ≃* Multiplicative (Fin d → ZMod 2))
      (ρ : G →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2)),
      ∀ (g : G) (a : A), β (φ g a) = Multiplicative.ofAdd
        ((((ρ g : Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) :
          Matrix (Fin d) (Fin d) (ZMod 2))).mulVec (Multiplicative.toAdd (β a))) := by
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hA _
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  have hfin : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (Additive A) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod] at h
    have hV' : Nat.card (Additive A) = 2 ^ d := hd
    rw [hV'] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b : Module.Basis (Fin d) (ZMod 2) (Additive A) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim
  let act : G → (Additive A →+ Additive A) := fun g =>
    MonoidHom.toAdditive (φ g).toMonoidHom
  let f : G →* Module.End (ZMod 2) (Additive A) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2 (act g)
      map_one' := LinearMap.ext fun x => by
        show Additive.ofMul ((φ 1) (Additive.toMul x)) = x
        rw [map_one]
        rfl
      map_mul' := fun g₁ g₂ => LinearMap.ext fun x => by
        show Additive.ofMul ((φ (g₁ * g₂)) (Additive.toMul x)) =
          Additive.ofMul ((φ g₁) ((φ g₂) (Additive.toMul x)))
        rw [map_mul]
        rfl }
  let β : A ≃* Multiplicative (Fin d → ZMod 2) :=
    { toFun := fun a => Multiplicative.ofAdd (b.equivFun (Additive.ofMul a))
      invFun := fun w => Additive.toMul (b.equivFun.symm (Multiplicative.toAdd w))
      left_inv := fun a => by simp
      right_inv := fun w => by
        show Multiplicative.ofAdd (b.equivFun (Additive.ofMul
          (Additive.toMul (b.equivFun.symm (Multiplicative.toAdd w))))) = w
        rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
        rfl
      map_mul' := fun a a' => by
        simp only [ofMul_mul, map_add, ofAdd_add] }
  let ρ : G →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2) :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toMonoidHom.comp
      f.toHomUnits
  refine ⟨β, ρ, fun g a => ?_⟩
  have h1 : (((ρ g : Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) :
      Matrix (Fin d) (Fin d) (ZMod 2))) = LinearMap.toMatrix b b (f g) := rfl
  rw [h1]
  show Multiplicative.ofAdd (b.equivFun (Additive.ofMul (φ g a))) =
    Multiplicative.ofAdd ((LinearMap.toMatrix b b (f g)).mulVec
      (b.equivFun (Additive.ofMul a)))
  congr 1
  have h3 : Additive.ofMul (φ g a) = f g (Additive.ofMul a) := rfl
  rw [h3, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact (LinearMap.toMatrix_mulVec_repr b b (f g) (Additive.ofMul a)).symm

end CFSG.Quasithin
