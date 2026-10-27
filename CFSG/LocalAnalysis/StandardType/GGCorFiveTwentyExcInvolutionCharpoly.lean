module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType

open Polynomial Module

section Involution

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem charpoly_neg_one :
    (-(LinearMap.id : V →ₗ[F] V)).charpoly = (X + 1) ^ finrank F V := by
  have h := LinearMap.charpoly_sub_smul (0 : Module.End F V) (1 : F)
  rw [LinearMap.charpoly_zero] at h
  have h0 : (-(LinearMap.id : V →ₗ[F] V)) = (0 - (1 : F) • 1 : Module.End F V) := by
    rw [← Module.End.one_eq_id]
    simp
  rw [h0, h]
  simp [Polynomial.pow_comp, Polynomial.X_comp]

theorem isCompl_ker_involution_of_two_ne_zero (h2 : (2 : F) ≠ 0) (f : V →ₗ[F] V)
    (hf : f ∘ₗ f = LinearMap.id) :
    IsCompl (LinearMap.ker (f - 1)) (LinearMap.ker (f + 1)) := by
  have hff : ∀ v, f (f v) = v := fun v => LinearMap.congr_fun hf v
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hv1 hv2
    have h1 : (f - 1) v = 0 := LinearMap.mem_ker.mp hv1
    have h2' : (f + 1) v = 0 := LinearMap.mem_ker.mp hv2
    have hfv : f v = v := sub_eq_zero.mp (by simpa using h1)
    have hvv : v + v = 0 := by
      have : f v + v = 0 := by simpa using h2'
      rwa [hfv] at this
    have htwo : (2 : F) • v = 0 := by rw [two_smul]; exact hvv
    exact (smul_eq_zero.mp htwo).resolve_left h2
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    have ha : (2 : F)⁻¹ • (v + f v) ∈ LinearMap.ker (f - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
      have hfa : f ((2 : F)⁻¹ • (v + f v)) = (2 : F)⁻¹ • (v + f v) := by
        rw [map_smul, map_add, hff, add_comm]
      rw [hfa, sub_self]
    have hb : (2 : F)⁻¹ • (v - f v) ∈ LinearMap.ker (f + 1) := by
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
      have hfb : f ((2 : F)⁻¹ • (v - f v)) = -((2 : F)⁻¹ • (v - f v)) := by
        rw [map_smul, map_sub, hff, show f v - v = -(v - f v) by abel, smul_neg]
      rw [hfb, neg_add_cancel]
    have hab : (2 : F)⁻¹ • (v + f v) + (2 : F)⁻¹ • (v - f v) = v := by
      rw [← smul_add]
      rw [show (v + f v) + (v - f v) = (2 : F) • v by rw [two_smul]; abel]
      rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hab]
    exact Submodule.add_mem_sup ha hb

theorem charpoly_involution (h2 : (2 : F) ≠ 0) (f : V →ₗ[F] V) (hf : f ∘ₗ f = LinearMap.id) :
    f.charpoly = (X - 1) ^ finrank F (LinearMap.ker (f - 1)) *
      (X + 1) ^ finrank F (LinearMap.ker (f + 1)) := by
  have hff : ∀ v, f (f v) = v := fun v => LinearMap.congr_fun hf v
  let Kp := LinearMap.ker (f - 1)
  let Km := LinearMap.ker (f + 1)
  have hc : IsCompl Kp Km := isCompl_ker_involution_of_two_ne_zero h2 f hf
  let e : (Kp × Km) ≃ₗ[F] V := Kp.prodEquivOfIsCompl Km hc
  let g : (Kp × Km) →ₗ[F] (Kp × Km) :=
    (LinearMap.id : Kp →ₗ[F] Kp).prodMap (-(LinearMap.id : Km →ₗ[F] Km))
  have hfa : ∀ a : Kp, f (a : V) = a := by
    intro a
    have ha : (f - 1) (a : V) = 0 := LinearMap.mem_ker.mp a.2
    rw [LinearMap.sub_apply, Module.End.one_apply] at ha
    exact sub_eq_zero.mp ha
  have hfb : ∀ b : Km, f (b : V) = -b := by
    intro b
    have hb : (f + 1) (b : V) = 0 := LinearMap.mem_ker.mp b.2
    rw [LinearMap.add_apply, Module.End.one_apply] at hb
    exact add_eq_zero_iff_eq_neg.mp hb
  have hconj : e.conj g = f := by
    ext v
    rw [LinearEquiv.conj_apply_apply]
    have hsum : ((e.symm v).1 : V) + ((e.symm v).2 : V) = v :=
      calc ((e.symm v).1 : V) + ((e.symm v).2 : V) = e (e.symm v) :=
            (Submodule.coe_prodEquivOfIsCompl' Kp Km hc (e.symm v)).symm
        _ = v := e.apply_symm_apply v
    conv_rhs => rw [← hsum, map_add, hfa, hfb]
    simp [e, g, Submodule.coe_prodEquivOfIsCompl', map_neg]
  have hmain : (e.conj g).charpoly = (X - 1) ^ finrank F Kp * (X + 1) ^ finrank F Km := by
    rw [LinearEquiv.charpoly_conj]
    rw [show g = (LinearMap.id : Kp →ₗ[F] Kp).prodMap
        (-(LinearMap.id : Km →ₗ[F] Km)) from rfl, LinearMap.charpoly_prodMap,
      show (LinearMap.id : Kp →ₗ[F] Kp) = (1 : Module.End F Kp) from Module.End.one_eq_id.symm,
      LinearMap.charpoly_one, charpoly_neg_one]
  conv_lhs => rw [← hconj]
  exact hmain

theorem finrank_ker_involution_add (h2 : (2 : F) ≠ 0) (f : V →ₗ[F] V)
    (hf : f ∘ₗ f = LinearMap.id) :
    finrank F (LinearMap.ker (f - 1)) + finrank F (LinearMap.ker (f + 1)) = finrank F V := by
  exact Submodule.finrank_add_eq_of_isCompl (isCompl_ker_involution_of_two_ne_zero h2 f hf)

end Involution

section MatrixForm

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

theorem charpoly_matrix_involution (h2 : (2 : F) ≠ 0) (M : Matrix n n F) (hM : M * M = 1) :
    M.charpoly = (X - 1) ^ finrank F (LinearMap.ker (M.mulVecLin - 1)) *
      (X + 1) ^ finrank F (LinearMap.ker (M.mulVecLin + 1)) := by
  rw [← Matrix.charpoly_mulVecLin]
  exact charpoly_involution h2 M.mulVecLin (by
    rw [← Matrix.mulVecLin_mul, hM, Matrix.mulVecLin_one])

theorem finrank_ker_matrix_involution_add (h2 : (2 : F) ≠ 0) (M : Matrix n n F)
    (hM : M * M = 1) :
    finrank F (LinearMap.ker (M.mulVecLin - 1)) + finrank F (LinearMap.ker (M.mulVecLin + 1)) =
      Fintype.card n := by
  rw [← Module.finrank_fintype_fun_eq_card (R := F) (η := n)]
  exact finrank_ker_involution_add h2 M.mulVecLin (by
    rw [← Matrix.mulVecLin_mul, hM, Matrix.mulVecLin_one])

end MatrixForm

end CFSG.StandardType

end
