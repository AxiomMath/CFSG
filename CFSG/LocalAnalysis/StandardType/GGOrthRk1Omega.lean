module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Block
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

public section

open Module

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]

noncomputable def rk1Omega (hD : finrank K D = 2) : LinearMap.BilinForm K D :=
  LinearMap.mk₂ K
    (fun x y => (Module.finBasisOfFinrankEq K D hD).repr x 0 *
        (Module.finBasisOfFinrankEq K D hD).repr y 1 -
      (Module.finBasisOfFinrankEq K D hD).repr x 1 * (Module.finBasisOfFinrankEq K D hD).repr y 0)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun a x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun a x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

@[simp] theorem rk1Omega_apply (hD : finrank K D = 2) (x y : D) :
    rk1Omega hD x y =
      (Module.finBasisOfFinrankEq K D hD).repr x 0 *
        (Module.finBasisOfFinrankEq K D hD).repr y 1 -
      (Module.finBasisOfFinrankEq K D hD).repr x 1 *
        (Module.finBasisOfFinrankEq K D hD).repr y 0 := by
  simp only [rk1Omega, LinearMap.mk₂_apply]

theorem rk1Omega_self (hD : finrank K D = 2) (x : D) : rk1Omega hD x x = 0 := by
  rw [rk1Omega_apply]
  ring

theorem rk1Omega_swap [CharP K 2] (hD : finrank K D = 2) (x y : D) :
    rk1Omega hD y x = rk1Omega hD x y := by
  rw [rk1Omega_apply, rk1Omega_apply, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring

theorem rk1Omega_map (hD : finrank K D = 2) (g : D →ₗ[K] D) (x y : D) :
    rk1Omega hD (g x) (g y) = LinearMap.det g * rk1Omega hD x y := by
  let b := Module.finBasisOfFinrankEq K D hD
  let M := LinearMap.toMatrix b b g
  have hx : b.repr (g x) = Matrix.mulVec M (b.repr x) := by
    simpa [M] using (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) g x).symm
  have hy : b.repr (g y) = Matrix.mulVec M (b.repr y) := by
    simpa [M] using (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) g y).symm
  have hdet : LinearMap.det g = Matrix.det M := by
    simp [M]
  rw [rk1Omega_apply, rk1Omega_apply]
  change b.repr (g x) 0 * b.repr (g y) 1 - b.repr (g x) 1 * b.repr (g y) 0 =
    LinearMap.det g * (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0)
  rw [hx, hy, hdet, Matrix.det_fin_two]
  simp only [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  ring

theorem rk1Omega_nondegenerate (hD : finrank K D = 2) {x : D} (hx : ∀ y, rk1Omega hD x y = 0) :
    x = 0 := by
  let b := Module.finBasisOfFinrankEq K D hD
  have h0 : b.repr x 0 = 0 := by
    have h := hx (b 1)
    rw [rk1Omega_apply] at h
    simpa [b, Basis.repr_self_apply] using h
  have h1 : b.repr x 1 = 0 := by
    have h := hx (b 0)
    rw [rk1Omega_apply] at h
    simpa [b, Basis.repr_self_apply] using h
  have hr : b.repr x = 0 := by
    ext i
    fin_cases i <;> simp [h0, h1]
  exact b.repr.map_eq_zero_iff.mp hr

theorem rk1Omega_eq_smul_id (hD : finrank K D = 2) {g : D →ₗ[K] D}
    (hg : ∀ x, rk1Omega hD x (g x) = 0) : ∃ a : K, g = a • LinearMap.id := by
  let b := Module.finBasisOfFinrankEq K D hD
  have hb01 : rk1Omega hD (b 0) (b 1) = 1 := by
    rw [rk1Omega_apply]
    simp [b]
  have hb10 : rk1Omega hD (b 1) (b 0) = -1 := by
    rw [rk1Omega_apply]
    simp [b]
  have hb00 : rk1Omega hD (b 0) (b 0) = 0 := rk1Omega_self hD _
  have hb11 : rk1Omega hD (b 1) (b 1) = 0 := rk1Omega_self hD _
  let a : K := b.repr (g (b 0)) 0
  let e : K := b.repr (g (b 1)) 1
  have h0 : b.repr (g (b 0)) 1 = 0 := by
    have h := hg (b 0)
    rw [rk1Omega_apply] at h
    simpa [b, Basis.repr_self_apply] using h
  have h1 : b.repr (g (b 1)) 0 = 0 := by
    have h := hg (b 1)
    rw [rk1Omega_apply] at h
    simpa [b, Basis.repr_self_apply] using h
  have hg0 : g (b 0) = a • b 0 := by
    conv_lhs => rw [← b.sum_repr (g (b 0))]
    rw [Fin.sum_univ_two, h0]
    simp [a]
  have hg1 : g (b 1) = e • b 1 := by
    conv_lhs => rw [← b.sum_repr (g (b 1))]
    rw [Fin.sum_univ_two, h1]
    simp [e]
  have hea : e = a := by
    have h := hg (b 0 + b 1)
    have hsum : g (b 0 + b 1) = a • b 0 + e • b 1 := by rw [map_add, hg0, hg1]
    rw [hsum] at h
    have hexp : rk1Omega hD (b 0 + b 1) (a • b 0 + e • b 1) = e - a := by
      simp [b, sub_eq_add_neg]
    rw [hexp] at h
    exact sub_eq_zero.mp h
  refine ⟨a, ?_⟩
  apply b.ext
  intro i
  fin_cases i
  · simpa using hg0
  · simpa [hea] using hg1

variable {c : D ≃ₗ[K] D} {p : ℕ}

theorem Rk1Block.quadForm_eq [CharP K 2] (hc : Rk1Block c p) (Q₀ : QuadraticForm K D)
    (hQ₀ : ∀ x, Q₀ (c x) = Q₀ x) :
    ∃ μ : K, ∀ x, Q₀ x = μ * rk1Omega hc.finrank_eq x (c x) := by
  obtain ⟨d, hd⟩ := hc.exists_linearIndependent
  let b : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank hd (by simp [hc.finrank_eq])
  have hb0 : b 0 = d := by simp [b]
  have hb1 : b 1 = c d := by simp [b]
  let t : K := LinearMap.trace K D (c : D →ₗ[K] D)
  have hneg : (-d : D) = d := by
    rw [← neg_one_smul K d, CharTwo.neg_eq (1 : K), one_smul]
  have hcd : (c : D →ₗ[K] D) (c d) = t • (c d) + d := by
    have hadd := congrArg (fun f : D →ₗ[K] D => f (c d)) hc.add_inv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hadd
    have hcinv : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) (c d) = d := by
      change c.symm (c d) = d
      exact c.symm_apply_apply d
    rw [hcinv] at hadd
    have h2 : (c : D →ₗ[K] D) (c d) = t • (c d) - d := eq_sub_of_add_eq hadd
    rw [h2, sub_eq_add_neg, hneg]
  let β : K := QuadraticMap.polar Q₀ d (c d)
  have hQgen : ∀ s u : K, Q₀ (s • d + u • (c d)) =
      s * s * Q₀ d + u * u * Q₀ (c d) + s * u * β := by
    intro s u
    rw [QuadraticMap.map_add Q₀, QuadraticMap.map_smul Q₀, QuadraticMap.map_smul Q₀]
    simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul, β]
    ring
  have hQgen' : ∀ s u : K, Q₀ (u • (c d) + s • d) =
      s * s * Q₀ d + u * u * Q₀ (c d) + s * u * β := by
    intro s u
    rw [add_comm, hQgen]
  have hβ : β = t * Q₀ d := by
    have h1 : Q₀ (t • (c d) + d) = Q₀ (c d) := by
      have h := hQ₀ (c d)
      change Q₀ ((c : D →ₗ[K] D) (c d)) = Q₀ (c d) at h
      rwa [hcd] at h
    have h3 : Q₀ (t • (c d) + d) =
        1 * 1 * Q₀ d + t * t * Q₀ (c d) + 1 * t * β := by
      simpa using hQgen' 1 t
    have h4 : 1 * 1 * Q₀ d + t * t * Q₀ (c d) + 1 * t * β = Q₀ (c d) := h3.symm.trans h1
    rw [hQ₀ d] at h4
    have h4' : 1 * 1 * Q₀ d + (t * t * Q₀ d + 1 * t * β) = 1 * 1 * Q₀ d + 0 := by
      rw [← add_assoc]
      simpa using h4
    have h5 : t * t * Q₀ d + 1 * t * β = 0 := add_left_cancel h4'
    have h6 : t * (t * Q₀ d + β) = 0 := by
      calc t * (t * Q₀ d + β) = t * t * Q₀ d + t * β := by ring
        _ = t * t * Q₀ d + 1 * t * β := by ring
        _ = 0 := h5
    have ht : t ≠ 0 := by simpa [t] using hc.trace_ne_zero
    have h7 : t * Q₀ d + β = 0 := (mul_eq_zero.mp h6).resolve_left ht
    have h8 : β = t * Q₀ d := by
      have h := congrArg (fun z => t * Q₀ d + z) h7
      rw [add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
      exact h
    exact h8
  have hW : rk1Omega hc.finrank_eq d (c d) ≠ 0 := by
    intro hW0
    have hzero : ∀ y, rk1Omega hc.finrank_eq d y = 0 := by
      intro y
      have hy : b.repr y 0 • d + b.repr y 1 • (c d) = y := by
        have h := b.sum_repr y
        rw [Fin.sum_univ_two, hb0, hb1] at h
        exact h
      rw [← hy]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [rk1Omega_self hc.finrank_eq d, hW0]
      ring
    have hd0 : d = 0 := rk1Omega_nondegenerate hc.finrank_eq hzero
    exact (hd.ne_zero 0) (by simpa using hd0)
  refine ⟨Q₀ d / rk1Omega hc.finrank_eq d (c d), ?_⟩
  intro x
  let s : K := b.repr x 0
  let u : K := b.repr x 1
  have hx : x = s • d + u • (c d) := by
    have h := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at h
    simpa [s, u] using h.symm
  have hcx : c x = u • d + (s + t * u) • (c d) := by
    rw [hx, map_add, map_smul, map_smul, show c (c d) = t • (c d) + d from hcd]
    simp only [smul_add, smul_smul]
    module
  have hQx : Q₀ x = Q₀ d * (s * s + t * s * u + u * u) := by
    rw [hx, hQgen s u, hQ₀ d, hβ]
    ring
  have hOmega : rk1Omega hc.finrank_eq x (c x) =
      (s * s + t * s * u + u * u) * rk1Omega hc.finrank_eq d (c d) := by
    rw [hcx, hx]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [rk1Omega_self hc.finrank_eq d, rk1Omega_self hc.finrank_eq (c d),
      (rk1Omega_swap hc.finrank_eq (c d) d).symm]
    ring
  rw [hQx, hOmega]
  field_simp [hW]

end OrthTorus

end CFSG.StandardType

end
