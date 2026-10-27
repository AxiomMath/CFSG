module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.CharP.Defs

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Module

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D]

structure Rk1Block (c : D ≃ₗ[K] D) (p : ℕ) : Prop where
  finrank_eq : finrank K D = 2
  prime : p.Prime
  ne_two : p ≠ 2
  pow_eq : c ^ p = 1
  fix : ∀ u, c u = u → u = 0
  twist : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹

variable {c : D ≃ₗ[K] D} {p : ℕ}

section
omit [CharP K 2]

private theorem charpoly_eq_finrank_two (h : finrank K D = 2) (f : Module.End K D) :
    f.charpoly = Polynomial.X ^ 2 - Polynomial.C (LinearMap.trace K D f) * Polynomial.X
      + Polynomial.C (LinearMap.det f) := by
  let b : Basis (Fin 2) K D := Module.finBasisOfFinrankEq K D h
  rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace K b f, LinearMap.det_toMatrix b f]

private theorem end_sq_sub_trace_smul_add_det (h : finrank K D = 2) (f : Module.End K D) :
    f ^ 2 - LinearMap.trace K D f • f + LinearMap.det f • (1 : Module.End K D) = 0 := by
  have hchar := charpoly_eq_finrank_two (K := K) (D := D) h f
  have h0 := LinearMap.aeval_self_charpoly f
  rw [hchar] at h0
  simpa [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] using h0

end

private theorem charP_end_two (hc : Rk1Block c p) : CharP (Module.End K D) 2 := by
  refine charP_of_injective_algebraMap (R := K) (A := Module.End K D) ?_ 2
  intro r s hrs
  by_contra hne
  have hne0 : r - s ≠ 0 := sub_ne_zero.mpr hne
  let b : Basis (Fin 2) K D := Module.finBasisOfFinrankEq K D hc.finrank_eq
  have h : r • (b 0) = s • (b 0) := by
    have h' := congrArg (fun f : Module.End K D => f (b 0)) hrs
    simpa [Algebra.algebraMap_eq_smul_one] using h'
  have hsub : (r - s) • (b 0) = 0 := by
    rw [sub_smul, h, sub_self]
  have hb : b 0 = 0 := by
    have h' := congrArg (fun x : D => (r - s)⁻¹ • x) hsub
    rw [smul_smul, inv_mul_cancel₀ hne0, one_smul, smul_zero] at h'
    exact h'
  exact (b.ne_zero 0) hb

section
omit [CharP K 2] [FiniteDimensional K D]

private theorem commute_algebraMap (r : K) (x : Module.End K D) :
    Commute (algebraMap K (Module.End K D) r) x :=
  Algebra.commutes r x

private theorem commute_smul_one (a : K) (x : Module.End K D) :
    Commute (a • (1 : Module.End K D)) x := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact commute_algebraMap a x

private theorem commute_smul_self (b : K) (x : Module.End K D) : Commute (b • x) x := by
  rw [Algebra.smul_def]
  exact (commute_algebraMap b x).mul_left (Commute.refl x)

private theorem commute_form (x : Module.End K D) (a b : K) :
    Commute (a • (1 : Module.End K D) + b • x) x :=
  (commute_smul_one a x).add_left (commute_smul_self b x)

private theorem commute_form_form (x : Module.End K D) (a b a' b' : K) :
    Commute (a • (1 : Module.End K D) + b • x) (a' • (1 : Module.End K D) + b' • x) := by
  let q := a • (1 : Module.End K D) + b • x
  have hx : Commute q x := commute_form x a b
  have h1 : Commute q (a' • (1 : Module.End K D)) := (commute_smul_one a' q).symm
  have h2 : Commute q (b' • x) := by
    rw [Algebra.smul_def]
    exact (commute_algebraMap b' q).symm |>.mul_right hx
  exact h1.add_right h2

private theorem sq_form [CharP (Module.End K D) 2] (a b : K) (x : Module.End K D) :
    (a • LinearMap.id + b • x) ^ 2 = a ^ 2 • LinearMap.id + b ^ 2 • x ^ 2 := by
  change (a • (1 : Module.End K D) + b • x) ^ 2 =
    a ^ 2 • (1 : Module.End K D) + b ^ 2 • x ^ 2
  have h1 : (a • (1 : Module.End K D)) ^ 2 = a ^ 2 • (1 : Module.End K D) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← map_pow, Algebra.algebraMap_eq_smul_one]
  have hmid : 2 * (a • (1 : Module.End K D)) * (b • x) = 0 := by
    rw [CharTwo.two_eq_zero, zero_mul, zero_mul]
  have h2 : (b • x) ^ 2 = b ^ 2 • x ^ 2 := by
    rw [Algebra.smul_def b x, Algebra.smul_def (b ^ 2) (x ^ 2), map_pow]
    exact (commute_algebraMap b x).mul_pow 2
  have hcomm : Commute (a • (1 : Module.End K D)) (b • x) := commute_smul_one a (b • x)
  rw [hcomm.add_sq, h1, hmid, h2]
  simp

end

section
omit [CharP K 2]

private theorem c_ne_inv (hc : Rk1Block c p) : c ≠ c⁻¹ := by
  intro h
  have hc2 : c ^ 2 = 1 := by
    have h' : c * c = 1 := by
      have h0 : c * c⁻¹ = 1 := mul_inv_cancel c
      rwa [← h] at h0
    rwa [pow_two]
  obtain ⟨k, hk⟩ := hc.prime.odd_of_ne_two hc.ne_two
  have hc1 : c = 1 := by
    have h' : (1 : D ≃ₗ[K] D) = c := by
      calc (1 : D ≃ₗ[K] D) = c ^ p := hc.pow_eq.symm
        _ = c ^ (2 * k + 1) := by rw [hk]
        _ = (c ^ 2) ^ k * c := by rw [pow_succ, pow_mul]
        _ = 1 ^ k * c := by rw [hc2]
        _ = c := by rw [one_pow, one_mul]
    exact h'.symm
  let b : Basis (Fin 2) K D := Module.finBasisOfFinrankEq K D hc.finrank_eq
  exact (b.ne_zero 0) (hc.fix (b 0) (by rw [hc1]; rfl))

end

section
omit [FiniteDimensional K D]

theorem Rk1Block.det_eq_one (hc : Rk1Block c p) : LinearMap.det (c : D →ₗ[K] D) = 1 := by
  obtain ⟨T, hT⟩ := hc.twist
  have hconj : LinearEquiv.det (T * c * T⁻¹) = LinearEquiv.det c := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  have hcu : LinearEquiv.det c = LinearEquiv.det c⁻¹ :=
    hconj.symm.trans (congrArg LinearEquiv.det hT)
  have h2 : LinearEquiv.det c * LinearEquiv.det c = 1 := by
    nth_rewrite 2 [hcu]
    rw [← map_mul, mul_inv_cancel, map_one]
  have h2' : LinearMap.det (c : D →ₗ[K] D) * LinearMap.det (c : D →ₗ[K] D) = 1 := by
    have h' := congrArg (fun u : Kˣ => (u : K)) h2
    simpa [LinearEquiv.coe_det] using h'
  have hx2 : LinearMap.det (c : D →ₗ[K] D) ^ 2 = 1 := by
    rw [pow_two]
    exact h2'
  exact CharTwo.sq_inj.mp (by rw [hx2, one_pow])

end

theorem Rk1Block.add_inv (hc : Rk1Block c p) :
    (c : D →ₗ[K] D) + ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) =
      LinearMap.trace K D (c : D →ₗ[K] D) • LinearMap.id := by
  have : CharP (Module.End K D) 2 := charP_end_two hc
  have hCH := end_sq_sub_trace_smul_add_det hc.finrank_eq (c : D →ₗ[K] D)
  have hCH' : (c : D →ₗ[K] D) * (c : D →ₗ[K] D) + LinearMap.trace K D (c : D →ₗ[K] D) •
      (c : D →ₗ[K] D) + 1 = 0 := by
    rw [Rk1Block.det_eq_one hc, one_smul, pow_two, CharTwo.sub_eq_add] at hCH
    exact hCH
  have hgf : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) * (c : D →ₗ[K] D) = 1 := by
    rw [← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one]
    rfl
  have key : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) *
      ((c : D →ₗ[K] D) * (c : D →ₗ[K] D) +
        LinearMap.trace K D (c : D →ₗ[K] D) • (c : D →ₗ[K] D) + 1) = 0 := by
    rw [hCH', mul_zero]
  rw [mul_add, mul_add, Algebra.mul_smul_comm, mul_one, ← mul_assoc, hgf, one_mul] at key
  have hres : (c : D →ₗ[K] D) + ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) +
      LinearMap.trace K D (c : D →ₗ[K] D) • 1 = 0 := by
    rw [← key]
    abel
  have hfinal : (c : D →ₗ[K] D) + ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) =
      LinearMap.trace K D (c : D →ₗ[K] D) • 1 := (CharTwo.add_eq_zero).mp hres
  exact hfinal

theorem Rk1Block.trace_ne_zero (hc : Rk1Block c p) : LinearMap.trace K D (c : D →ₗ[K] D) ≠ 0 := by
  have : CharP (Module.End K D) 2 := charP_end_two hc
  intro ht
  apply c_ne_inv hc
  have h := Rk1Block.add_inv hc
  rw [ht, zero_smul] at h
  have hgf : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) = (c : D →ₗ[K] D) :=
    ((CharTwo.add_eq_zero).mp h).symm
  have : c⁻¹ = c := LinearEquiv.toLinearMap_injective hgf
  exact this.symm

theorem Rk1Block.exists_linearIndependent (hc : Rk1Block c p) :
    ∃ d : D, LinearIndependent K ![d, c d] := by
  by_contra h
  simp only [not_exists] at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (R := K) (V := D) (f := (c : D →ₗ[K] D)) h
  have htrace : LinearMap.trace K D (c : D →ₗ[K] D) = 0 := by
    have h2 : (finrank K D : K) = 0 := by
      rw [hc.finrank_eq]
      exact CharTwo.two_eq_zero
    rw [ha, map_smul, LinearMap.trace_one, h2, smul_zero]
  exact Rk1Block.trace_ne_zero hc htrace

private theorem smul_one_add_smul_eq_zero (hc : Rk1Block c p) {α β : K}
    (h : α • (1 : Module.End K D) + β • (c : D →ₗ[K] D) = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨d, hd⟩ := Rk1Block.exists_linearIndependent hc
  have hd' : α • d + β • (c d) = 0 := by
    have h' := congrArg (fun f : Module.End K D => f d) h
    simpa [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] using h'
  exact (LinearIndependent.pair_iff.mp hd) α β hd'

theorem Rk1Block.commute_eq (hc : Rk1Block c p) {g : D →ₗ[K] D}
    (hg : g ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ g) :
    ∃ a b : K, g = a • LinearMap.id + b • (c : D →ₗ[K] D) := by
  obtain ⟨d, hd⟩ := Rk1Block.exists_linearIndependent hc
  let B : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank hd (by rw [Fintype.card_fin, hc.finrank_eq])
  have hB : ⇑B = ![d, c d] := coe_basisOfLinearIndependentOfCardEqFinrank hd _
  have h0 : B 0 = d := by rw [hB]; rfl
  have h1 : B 1 = c d := by rw [hB]; rfl
  have hsum := B.sum_repr (g d)
  rw [Fin.sum_univ_two, h0, h1] at hsum
  let a : K := (B.repr (g d)) 0
  let b : K := (B.repr (g d)) 1
  have hsum' : a • d + b • (c d) = g d := by
    simpa [a, b] using hsum
  refine ⟨a, b, ?_⟩
  apply B.ext
  rw [Fin.forall_fin_two]
  constructor
  · rw [h0]
    simpa [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] using hsum'.symm
  · simp only [h1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hgc : g (c d) = (c : D →ₗ[K] D) (g d) := by
      have h' := congrArg (fun k : Module.End K D => k d) hg
      simpa [LinearMap.comp_apply] using h'
    rw [hgc, ← hsum', map_add, map_smul, map_smul]
    simp

theorem Rk1Block.mul_comm_of_commute (hc : Rk1Block c p) {g g' : Module.End K D}
    (hg : g ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ g)
    (hg' : g' ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ g') : g * g' = g' * g := by
  obtain ⟨a, b, rfl⟩ := Rk1Block.commute_eq hc hg
  obtain ⟨a', b', rfl⟩ := Rk1Block.commute_eq hc hg'
  exact (commute_form_form (c : D →ₗ[K] D) a b a' b').eq

theorem Rk1Block.eq_one_of_commute (hc : Rk1Block c p) {u : Module.End K D}
    (hu : u ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ u) {k : ℕ} (hk : u ^ (2 ^ k) = 1) :
    u = 1 := by
  have : CharP (Module.End K D) 2 := charP_end_two hc
  have hnc : (u - 1) ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ (u - 1) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id,
      LinearMap.id_comp, LinearMap.comp_id]
    rw [hu]
  obtain ⟨a, b, hn_eq⟩ := Rk1Block.commute_eq hc hnc
  have hn_pow : (u - 1) ^ (2 ^ k) = 0 := by
    have h := add_pow_char_pow_of_commute (p := 2) (n := k) (Commute.one_right u)
    rw [show u - 1 = u + 1 by rw [CharTwo.sub_eq_add], h, hk, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have hnil : IsNilpotent (u - 1) := ⟨2 ^ k, hn_pow⟩
  have hchar := (LinearMap.isNilpotent_iff_charpoly (u - 1)).mp hnil
  rw [hc.finrank_eq] at hchar
  have hsq : (u - 1) ^ 2 = 0 := by
    have h' := LinearMap.aeval_self_charpoly (u - 1)
    rw [hchar] at h'
    simpa using h'
  have hc2 : (c : D →ₗ[K] D) ^ 2 =
      LinearMap.trace K D (c : D →ₗ[K] D) • (c : D →ₗ[K] D) + 1 := by
    have hgf : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) * (c : D →ₗ[K] D) = 1 := by
      rw [← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel, LinearEquiv.coe_toLinearMap_one]
      rfl
    have h := congrArg (fun z : Module.End K D => z * (c : D →ₗ[K] D)) (Rk1Block.add_inv hc)
    rw [add_mul, hgf, Algebra.smul_mul_assoc, ← Module.End.one_eq_id, one_mul] at h
    rw [sq]
    have h' := congrArg (fun z : Module.End K D => z + 1) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using h'
  have hn2 : (u - 1) * (u - 1) = (a ^ 2 + b ^ 2) • (1 : Module.End K D) +
      (b ^ 2 * LinearMap.trace K D (c : D →ₗ[K] D)) • (c : D →ₗ[K] D) := by
    rw [hn_eq, ← sq, sq_form, hc2, smul_add, smul_smul, add_smul, Module.End.one_eq_id]
    abel
  have hzero : (a ^ 2 + b ^ 2) • (1 : Module.End K D) +
      (b ^ 2 * LinearMap.trace K D (c : D →ₗ[K] D)) • (c : D →ₗ[K] D) = 0 := by
    rw [← hn2, ← sq, hsq]
  obtain ⟨ha0, hb0⟩ := smul_one_add_smul_eq_zero hc hzero
  have ht : LinearMap.trace K D (c : D →ₗ[K] D) ≠ 0 := Rk1Block.trace_ne_zero hc
  have hb2 : b ^ 2 = 0 := (mul_eq_zero.mp hb0).resolve_right ht
  have hb : b = 0 := sq_eq_zero_iff.mp hb2
  have ha2 : a ^ 2 = 0 := by
    rw [hb] at ha0
    simpa using ha0
  have ha : a = 0 := sq_eq_zero_iff.mp ha2
  have hform0 : a • LinearMap.id + b • (c : D →ₗ[K] D) = 0 := by
    rw [ha, hb, zero_smul, zero_smul, add_zero]
  rw [hform0] at hn_eq
  exact sub_eq_zero.mp hn_eq

end OrthTorus

end CFSG.StandardType

end
