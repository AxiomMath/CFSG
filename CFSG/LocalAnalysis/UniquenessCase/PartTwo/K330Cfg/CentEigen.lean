module

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310u
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

theorem finrank_eq_sum_eigen {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (x : V ≃ₗ[F] V) (hx : x ^ 3 = 1) (ω : F) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (W : Submodule F V) (hW : ∀ w ∈ W, x w ∈ W) :
    Module.finrank F ↥W =
      Module.finrank F ↥(W ⊓ LinearMap.ker ((x : V →ₗ[F] V) - 1)) +
      Module.finrank F ↥(W ⊓ LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) +
      Module.finrank F ↥(W ⊓ LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) := by
  have hsum : (1 : F) + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
      rw [show (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 by ring, hω3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  have h3 : (3 : F) ≠ 0 := by
    intro h30
    have hsq : (ω - 1) ^ 2 = 0 := by
      rw [show (ω - 1) ^ 2 = (1 + ω + ω ^ 2) - 3 * ω by ring, hsum, h30]
      ring
    exact hω1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hx3 : ((x : V →ₗ[F] V) ^ 3) = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V))
      x 3
    rw [hx, map_one] at h
    exact h.symm
  have hW' : ∀ w ∈ W, ((x : V →ₗ[F] V)) w ∈ W := fun w hw => hW w hw
  have h := _root_.CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u.finrank_eq_add_add
    (K := F) (V := V) h3 hω1 hω3 hx3 hW'
  have e1 : W ⊓ Module.End.eigenspace (↑x) 1 =
      W ⊓ LinearMap.ker ((↑x : V →ₗ[F] V) - (1 : V →ₗ[F] V)) := by
    rw [Module.End.eigenspace_def, one_smul]
  have e2 : W ⊓ Module.End.eigenspace (↑x) ω =
      W ⊓ LinearMap.ker ((↑x : V →ₗ[F] V) - ω • (1 : V →ₗ[F] V)) := by
    rw [Module.End.eigenspace_def]
  have e3 : W ⊓ Module.End.eigenspace (↑x) (ω ^ 2) =
      W ⊓ LinearMap.ker ((↑x : V →ₗ[F] V) - ω ^ 2 • (1 : V →ₗ[F] V)) := by
    rw [Module.End.eigenspace_def]
  rw [e1, e2, e3] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
