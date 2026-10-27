module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.SpecialLinearGroup
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.StandardType.ZS

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem pow_le_card_of_sl_le {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] {n : ℕ}
    (hn : Module.finrank (ZMod p) V = n) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hSL : ∀ g : V ≃ₗ[ZMod p] V, LinearEquiv.det g = 1 → g ∈ A) :
    p ^ (n * (n - 1) / 2) ≤ Nat.card A := by
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite A :=
    Finite.of_injective (fun f : A => ((f : V ≃ₗ[ZMod p] V) : V → V))
      (fun f g h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have hcard : Nat.card (unitriangular n (ZMod p)) ≤ Nat.card A := by
    let b : Module.Basis (Fin n) (ZMod p) V := Module.finBasisOfFinrankEq (ZMod p) V hn
    let e := Matrix.SpecialLinearGroup.toLin_equiv b
    let f : unitriangular n (ZMod p) → A := fun u =>
      ⟨(e (u : Matrix.SpecialLinearGroup (Fin n) (ZMod p)) : V ≃ₗ[ZMod p] V),
        hSL _ (e (u : Matrix.SpecialLinearGroup (Fin n) (ZMod p))).2⟩
    have hf : Function.Injective f := by
      intro u v huv
      have h1 : (e (u : Matrix.SpecialLinearGroup (Fin n) (ZMod p)) : V ≃ₗ[ZMod p] V) =
          (e (v : Matrix.SpecialLinearGroup (Fin n) (ZMod p)) : V ≃ₗ[ZMod p] V) :=
        congrArg (fun x : A => (x : V ≃ₗ[ZMod p] V)) huv
      exact Subtype.ext (e.injective (Subtype.ext h1))
    exact Nat.card_le_card_of_injective f hf
  calc p ^ (n * (n - 1) / 2) = Nat.card (unitriangular n (ZMod p)) := by
        rw [card_unitriangular, show Nat.card (ZMod p) = p by
          rw [Nat.card_eq_fintype_card, ZMod.card]]
    _ ≤ Nat.card A := hcard

end CFSG.StandardType.ZS
