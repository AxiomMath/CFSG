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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.Quasithin.Vol2.Ch10.SecA

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem nonempty_mulEquiv_pi_of_sq_eq_one {W : Type*} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hcard : Nat.card W = 2 ^ d) :
    Nonempty (W ≃* Multiplicative (Fin d → ZMod 2)) := by
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule fun a => by
    change Additive.ofMul ((Additive.toMul a) ^ 2) = 0
    rw [h2]
    rfl
  have hfin : Module.finrank (ZMod 2) (Additive W) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h
    have hW : Nat.card (Additive W) = Nat.card W := rfl
    rw [hW, hcard] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hfin' : Module.finrank (ZMod 2) (Additive W) =
      Module.finrank (ZMod 2) (Fin d → ZMod 2) := by
    rw [hfin, Module.finrank_fin_fun]
  exact ⟨AddEquiv.toMultiplicativeRight (LinearEquiv.ofFinrankEq _ _ hfin').toAddEquiv⟩

@[expose] noncomputable def mulAutPiEquivLinearEquiv (d : ℕ) :
    MulAut (Multiplicative (Fin d → ZMod 2)) ≃*
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) where
  toFun φ :=
    { ((AddEquiv.toMultiplicative.symm φ :
          (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).toAddMonoidHom.toZModLinearMap 2) with
      invFun := (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).symm
      left_inv :=
        (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).left_inv
      right_inv :=
        (AddEquiv.toMultiplicative.symm φ : (Fin d → ZMod 2) ≃+ (Fin d → ZMod 2)).right_inv }
  invFun ψ := AddEquiv.toMultiplicative ψ.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def mulAutPiEquivGL (d : ℕ) :
    MulAut (Multiplicative (Fin d → ZMod 2)) ≃* GL (Fin d) (ZMod 2) :=
  (mulAutPiEquivLinearEquiv d).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2)).symm.trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := ZMod 2)).symm)

theorem card_mulAut_of_sq_eq_one {W : Type*} [CommGroup W] [Finite W]
    (h2 : ∀ w : W, w ^ 2 = 1) {d : ℕ} (hcard : Nat.card W = 2 ^ d) :
    Nat.card (MulAut W) = Nat.card (GL (Fin d) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_pi_of_sq_eq_one h2 hcard
  exact Nat.card_congr ((MulAut.congr e).trans (mulAutPiEquivGL d)).toEquiv

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three]

end CFSG.Quasithin.Vol2.Ch10.SecA
