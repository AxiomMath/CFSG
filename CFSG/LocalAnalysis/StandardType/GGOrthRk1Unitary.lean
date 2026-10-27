module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Omega

public section

open Module

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] {c : D ≃ₗ[K] D} {p : ℕ}

private lemma add_self_eq_zero_module (K : Type) [Semiring K] [CharP K 2] {D : Type}
    [AddCommMonoid D] [Module K D] (v : D) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

private lemma eq_add_of_add_eq_D (K : Type) [Field K] [CharP K 2] {D : Type} [AddCommGroup D]
    [Module K D] {a b t : D} (h : a + b = t) : b = t + a := by
  have hvv : ∀ v : D, v + v = 0 := add_self_eq_zero_module K
  calc b = a + (a + b) := by rw [← add_assoc, hvv, zero_add]
    _ = a + t := by rw [h]
    _ = t + a := add_comm ..

private lemma mul_repr (K : Type) [Field K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
    {c : D ≃ₗ[K] D} {t : K}
    (hc2 : (c : Module.End K D) * (c : Module.End K D) = t • (c : Module.End K D) + (1 : Module.End K D))
    (a b e f : K) :
    (a • (1 : Module.End K D) + b • (c : Module.End K D)) *
        (e • (1 : Module.End K D) + f • (c : Module.End K D)) =
      (a * e + b * f) • (1 : Module.End K D) + (a * f + b * e + t * b * f) • (c : Module.End K D) := by
  have hc2x : ∀ x : D, (c : D ≃ₗ[K] D) ((c : D ≃ₗ[K] D) x) =
      t • ((c : D ≃ₗ[K] D) x) + x := by
    intro x
    have h := congrArg (fun g : Module.End K D => g x) hc2
    simpa using h
  ext x
  simp [hc2x, smul_add, add_smul, smul_smul, mul_add, add_mul]
  module

omit [FiniteDimensional K D] in
private lemma coeffs_eq_of_repr {d : D}
    (hd : LinearIndependent K ![d, (c : D ≃ₗ[K] D) d]) {u v w z : K}
    (h : u • (1 : Module.End K D) + v • (c : Module.End K D) =
      w • (1 : Module.End K D) + z • (c : Module.End K D)) :
    u = w ∧ v = z := by
  have h' : u • d + v • ((c : Module.End K D) d) =
      w • d + z • ((c : Module.End K D) d) := by
    simpa using congrArg (fun g : Module.End K D => g d) h
  have hzero : (u + w) • d + (v + z) • ((c : Module.End K D) d) = 0 := by
    have h2 : (u • d + v • ((c : Module.End K D) d)) +
        (w • d + z • ((c : Module.End K D) d)) = 0 := by
      rw [h']
      exact add_self_eq_zero_module K _
    calc (u + w) • d + (v + z) • ((c : Module.End K D) d)
        = (u • d + v • ((c : Module.End K D) d)) +
            (w • d + z • ((c : Module.End K D) d)) := by module
      _ = 0 := h2
  have hp := (LinearIndependent.pair_iff.mp hd) (u + w) (v + z) hzero
  exact ⟨CharTwo.add_eq_zero.mp hp.1, CharTwo.add_eq_zero.mp hp.2⟩

private lemma scalar_algebra {K : Type} [Field K] [CharP K 2] {a0 a1 b0 b1 c0 c1 e0 e1 t : K}
    (ht : t ≠ 0)
    (h1 : a0 * c1 + a1 * c0 = 0) (h2 : b0 * e1 + b1 * e0 = 0)
    (h3a : a0 * e0 + t * a1 * e0 + a1 * e1 + c0 * b0 + t * c1 * b0 + c1 * b1 = 1)
    (h3b : a0 * e1 + a1 * e0 + c0 * b1 + c1 * b0 = 0)
    (h4a : a0 * e0 + a1 * e1 + b0 * c0 + b1 * c1 = 1)
    (h4b : a0 * e1 + a1 * e0 + t * a1 * e1 + b0 * c1 + b1 * c0 + t * b1 * c1 = 0) :
    a1 = 0 ∧ b1 = 0 ∧ c1 = 0 ∧ e1 = 0 := by
  have hA : t * (a1 * e0 + c1 * b0) = 0 := by linear_combination h3a - h4a
  have hA' : a1 * e0 + c1 * b0 = 0 := (mul_eq_zero.mp hA).resolve_left ht
  have hAe : a1 * e0 = c1 * b0 := CharTwo.add_eq_zero.mp hA'
  have hB : t * (a1 * e1 + b1 * c1) = 0 := by linear_combination h4b - h3b
  have hB' : a1 * e1 + b1 * c1 = 0 := (mul_eq_zero.mp hB).resolve_left ht
  have h5 : a0 * e0 + b0 * c0 = 1 := by linear_combination h4a - hB'
  have h6 : a0 * e1 + c0 * b1 = 0 := by linear_combination h3b - hA'
  have h6e : a0 * e1 = c0 * b1 := CharTwo.add_eq_zero.mp h6
  have h2e : b0 * e1 = b1 * e0 := CharTwo.add_eq_zero.mp h2
  have h1e : a0 * c1 = a1 * c0 := CharTwo.add_eq_zero.mp h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc a1 = (a0 * e0 + b0 * c0) * a1 := by rw [h5, one_mul]
      _ = a0 * a1 * e0 + b0 * a1 * c0 := by ring
      _ = a0 * (a1 * e0) + b0 * (a1 * c0) := by ring
      _ = a0 * (c1 * b0) + b0 * (a0 * c1) := by rw [hAe, h1e]
      _ = 0 := by
          have hh : a0 * (c1 * b0) + b0 * (a0 * c1) = a0 * b0 * c1 + a0 * b0 * c1 := by ring
          rw [hh, CharTwo.add_self_eq_zero]
  · calc b1 = (a0 * e0 + b0 * c0) * b1 := by rw [h5, one_mul]
      _ = a0 * b1 * e0 + b0 * b1 * c0 := by ring
      _ = a0 * (b1 * e0) + b0 * (c0 * b1) := by ring
      _ = a0 * (b0 * e1) + b0 * (a0 * e1) := by rw [← h2e, h6e]
      _ = 0 := by
          have hh : a0 * (b0 * e1) + b0 * (a0 * e1) = a0 * b0 * e1 + a0 * b0 * e1 := by ring
          rw [hh, CharTwo.add_self_eq_zero]
  · calc c1 = (a0 * e0 + b0 * c0) * c1 := by rw [h5, one_mul]
      _ = a0 * c1 * e0 + b0 * c1 * c0 := by ring
      _ = a1 * c0 * e0 + b0 * c1 * c0 := by rw [h1e]
      _ = a1 * c0 * e0 + c0 * (b0 * c1) := by ring
      _ = a1 * c0 * e0 + c0 * (a1 * e0) := by rw [mul_comm b0 c1, hAe.symm]
      _ = 0 := by
          have hh : a1 * c0 * e0 + c0 * (a1 * e0) = a1 * e0 * c0 + a1 * e0 * c0 := by ring
          rw [hh, CharTwo.add_self_eq_zero]
  · calc e1 = (a0 * e0 + b0 * c0) * e1 := by rw [h5, one_mul]
      _ = a0 * e0 * e1 + b0 * c0 * e1 := by ring
      _ = e0 * (a0 * e1) + c0 * (b0 * e1) := by ring
      _ = e0 * (c0 * b1) + c0 * (b1 * e0) := by rw [h6e, h2e]
      _ = 0 := by
          have hh : e0 * (c0 * b1) + c0 * (b1 * e0) = c0 * b1 * e0 + c0 * b1 * e0 := by ring
          rw [hh, CharTwo.add_self_eq_zero]

theorem Rk1Block.scalar_of_unitary (hc : Rk1Block c p) {A B C E : Module.End K D}
    (hA : A ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ A)
    (hB : B ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ B)
    (hC : C ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ C)
    (hE : E ∘ₗ (c : D →ₗ[K] D) = (c : D →ₗ[K] D) ∘ₗ E)
    (h1 : ∀ x, rk1Omega hc.finrank_eq (A x) (C x) = 0)
    (h2 : ∀ y, rk1Omega hc.finrank_eq (B y) (E y) = 0)
    (h3 : ∀ x y, rk1Omega hc.finrank_eq (A x) (E y) + rk1Omega hc.finrank_eq (B y) (C x) =
      rk1Omega hc.finrank_eq x y)
    (h4 : A * E + B * C = 1) :
    ∃ a b c' e : K, A = a • LinearMap.id ∧ B = b • LinearMap.id ∧ C = c' • LinearMap.id ∧
      E = e • LinearMap.id := by
  obtain ⟨d, hd⟩ := hc.exists_linearIndependent
  have hd' : LinearIndependent K ![d, (c : D →ₗ[K] D) d] := by simpa using hd
  set t : K := LinearMap.trace K D (c : D →ₗ[K] D) with ht_def
  have ht : t ≠ 0 := by rw [ht_def]; exact hc.trace_ne_zero
  have hdet : LinearMap.det (c : D →ₗ[K] D) = 1 := hc.det_eq_one
  have hadd := hc.add_inv (c := c) (p := p)
  rw [← ht_def] at hadd
  have hcinv : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) = t • (1 : Module.End K D) + (c : D →ₗ[K] D) := by
    ext y
    have hy : (c : D →ₗ[K] D) y + ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) y = t • y := by
      have h' := congrArg (fun g : Module.End K D => g y) hadd
      simpa using h'
    simpa using eq_add_of_add_eq_D K hy
  have hc2 : (c : Module.End K D) * (c : Module.End K D) = t • (c : Module.End K D) + (1 : Module.End K D) := by
    ext y
    have hy : t • ((c : D →ₗ[K] D) y) + ((c : D →ₗ[K] D) * (c : D →ₗ[K] D)) y = y := by
      have h' := congrArg (fun g : Module.End K D => g ((c : D →ₗ[K] D) y)) hcinv
      simpa using h'.symm
    have hh := eq_add_of_add_eq_D K hy
    simpa [add_comm] using hh
  have hωc : ∀ x y : D, rk1Omega hc.finrank_eq ((c : D →ₗ[K] D) x) y =
      t * rk1Omega hc.finrank_eq x y + rk1Omega hc.finrank_eq x ((c : D →ₗ[K] D) y) := by
    intro x y
    have hmap := rk1Omega_map hc.finrank_eq (c : D →ₗ[K] D) x
      (((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) y)
    rw [hdet, one_mul] at hmap
    have hcc : (c : D →ₗ[K] D) (((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) y) = y := by simp
    rw [hcc] at hmap
    rw [hmap]
    have hpt : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) y = t • y + (c : D →ₗ[K] D) y := by
      have h' := congrArg (fun g : Module.End K D => g y) hcinv
      simpa using h'
    rw [hpt]
    simp [map_add, map_smul, smul_eq_mul]
  have hωlin : ∀ (a b : K) (x y : D),
      rk1Omega hc.finrank_eq ((a • (1 : Module.End K D) + b • (c : Module.End K D)) x) y =
      rk1Omega hc.finrank_eq x (((a + t * b) • (1 : Module.End K D) +
        b • (c : Module.End K D)) y) := by
    intro a b x y
    have hx : ((a • (1 : Module.End K D) + b • (c : Module.End K D)) x) =
        a • x + b • ((c : Module.End K D) x) := by simp
    rw [hx]
    have hx1 : rk1Omega hc.finrank_eq (a • x + b • ((c : Module.End K D) x)) y =
        a * (rk1Omega hc.finrank_eq x y) +
          b * (rk1Omega hc.finrank_eq ((c : Module.End K D) x) y) := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hx1, hωc x y]
    have hy : (((a + t * b) • (1 : Module.End K D) + b • (c : Module.End K D)) y) =
        (a + t * b) • y + b • ((c : Module.End K D) y) := by simp
    rw [hy]
    have hy1 : rk1Omega hc.finrank_eq x ((a + t * b) • y + b • ((c : Module.End K D) y)) =
        (a + t * b) * (rk1Omega hc.finrank_eq x y) +
          b * (rk1Omega hc.finrank_eq x ((c : Module.End K D) y)) := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hy1]
    ring
  obtain ⟨a0, a1, hA'⟩ := hc.commute_eq hA
  obtain ⟨b0, b1, hB'⟩ := hc.commute_eq hB
  obtain ⟨c0, c1, hC'⟩ := hc.commute_eq hC
  obtain ⟨e0, e1, hE'⟩ := hc.commute_eq hE
  have hA1 : A = a0 • (1 : Module.End K D) + a1 • (c : Module.End K D) := hA'
  have hB1 : B = b0 • (1 : Module.End K D) + b1 • (c : Module.End K D) := hB'
  have hC1 : C = c0 • (1 : Module.End K D) + c1 • (c : Module.End K D) := hC'
  have hE1 : E = e0 • (1 : Module.End K D) + e1 • (c : Module.End K D) := hE'
  have h1'' : ∀ x, rk1Omega hc.finrank_eq x
      ((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * C) x) = 0 := by
    intro x
    have h := h1 x
    rw [hA1] at h
    rw [hωlin a0 a1 x (C x)] at h
    simpa using h
  obtain ⟨μA, hμA⟩ := rk1Omega_eq_smul_id hc.finrank_eq h1''
  have hμA1 : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * C =
      μA • (1 : Module.End K D) := hμA
  have hreprAC : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * C =
      ((a0 + t * a1) * c0 + a1 * c1) • (1 : Module.End K D) +
        ((a0 + t * a1) * c1 + a1 * c0 + t * a1 * c1) • (c : Module.End K D) := by
    rw [hC1]
    exact mul_repr K hc2 (a0 + t * a1) a1 c0 c1
  have hraw1 : (a0 + t * a1) * c1 + a1 * c0 + t * a1 * c1 = 0 := by
    have h : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * C =
        μA • (1 : Module.End K D) := hμA1
    rw [hreprAC] at h
    have h' : ((a0 + t * a1) * c0 + a1 * c1) • (1 : Module.End K D) +
          ((a0 + t * a1) * c1 + a1 * c0 + t * a1 * c1) • (c : Module.End K D) =
        μA • (1 : Module.End K D) + (0 : K) • (c : Module.End K D) := by
      simpa using h
    have := (coeffs_eq_of_repr hd' h').2
    simpa using this
  have h1eq : a0 * c1 + a1 * c0 = 0 := by
    linear_combination hraw1 - (t * a1 * c1) * (CharTwo.two_eq_zero (R := K))
  have h2'' : ∀ y, rk1Omega hc.finrank_eq y
      ((((b0 + t * b1) • (1 : Module.End K D) + b1 • (c : Module.End K D)) * E) y) = 0 := by
    intro y
    have h := h2 y
    rw [hB1] at h
    rw [hωlin b0 b1 y (E y)] at h
    simpa using h
  obtain ⟨μB, hμB⟩ := rk1Omega_eq_smul_id hc.finrank_eq h2''
  have hμB1 : ((b0 + t * b1) • (1 : Module.End K D) + b1 • (c : Module.End K D)) * E =
      μB • (1 : Module.End K D) := hμB
  have hreprBE : ((b0 + t * b1) • (1 : Module.End K D) + b1 • (c : Module.End K D)) * E =
      ((b0 + t * b1) * e0 + b1 * e1) • (1 : Module.End K D) +
        ((b0 + t * b1) * e1 + b1 * e0 + t * b1 * e1) • (c : Module.End K D) := by
    rw [hE1]
    exact mul_repr K hc2 (b0 + t * b1) b1 e0 e1
  have hraw2 : (b0 + t * b1) * e1 + b1 * e0 + t * b1 * e1 = 0 := by
    have h : ((b0 + t * b1) • (1 : Module.End K D) + b1 • (c : Module.End K D)) * E =
        μB • (1 : Module.End K D) := hμB1
    rw [hreprBE] at h
    have h' : ((b0 + t * b1) * e0 + b1 * e1) • (1 : Module.End K D) +
          ((b0 + t * b1) * e1 + b1 * e0 + t * b1 * e1) • (c : Module.End K D) =
        μB • (1 : Module.End K D) + (0 : K) • (c : Module.End K D) := by
      simpa using h
    have := (coeffs_eq_of_repr hd' h').2
    simpa using this
  have h2eq : b0 * e1 + b1 * e0 = 0 := by
    linear_combination hraw2 - (t * b1 * e1) * (CharTwo.two_eq_zero (R := K))
  have h3' : ∀ x y, rk1Omega hc.finrank_eq x
        ((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E) y) +
      rk1Omega hc.finrank_eq x
        ((((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y) =
      rk1Omega hc.finrank_eq x y := by
    intro x y
    have h := h3 x y
    rw [hA1, hB1, hC1, hE1] at h
    have h1t : rk1Omega hc.finrank_eq ((a0 • (1 : Module.End K D) + a1 • (c : Module.End K D)) x)
        ((e0 • (1 : Module.End K D) + e1 • (c : Module.End K D)) y) =
        rk1Omega hc.finrank_eq x (((a0 + t * a1) • (1 : Module.End K D) +
          a1 • (c : Module.End K D)) ((e0 • (1 : Module.End K D) +
            e1 • (c : Module.End K D)) y)) := hωlin a0 a1 x _
    have h2t : rk1Omega hc.finrank_eq ((b0 • (1 : Module.End K D) + b1 • (c : Module.End K D)) y)
        ((c0 • (1 : Module.End K D) + c1 • (c : Module.End K D)) x) =
        rk1Omega hc.finrank_eq x (((c0 + t * c1) • (1 : Module.End K D) +
          c1 • (c : Module.End K D)) ((b0 • (1 : Module.End K D) +
            b1 • (c : Module.End K D)) y)) := by
      rw [rk1Omega_swap hc.finrank_eq ((c0 • (1 : Module.End K D) +
        c1 • (c : Module.End K D)) x) ((b0 • (1 : Module.End K D) +
          b1 • (c : Module.End K D)) y)]
      exact hωlin c0 c1 x _
    rw [h1t, h2t] at h
    rw [hE1, hB1]
    exact h
  have hsum : ∀ y, ((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
      ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y) = y := by
    intro y
    have hz : ∀ x, rk1Omega hc.finrank_eq x
        (((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
          ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y) + y) = 0 := by
      intro x
      have hlin : rk1Omega hc.finrank_eq x
          (((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
            ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y)) =
          rk1Omega hc.finrank_eq x y := by
        rw [LinearMap.add_apply, map_add]
        exact h3' x y
      have hc := congrArg (fun z => z + rk1Omega hc.finrank_eq x y) hlin
      rw [CharTwo.add_self_eq_zero (R := K)] at hc
      rw [map_add]
      exact hc
    have hnd : (((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
        ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y) + y) = 0 := by
      apply rk1Omega_nondegenerate hc.finrank_eq
        (x := (((((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
          ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B) y) + y))
      intro w
      rw [rk1Omega_swap hc.finrank_eq]
      exact hz w
    have hh := eq_add_of_add_eq_D K (t := 0) hnd
    simpa using hh.symm
  have hσ : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
      ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B = 1 := by
    ext y
    exact hsum y
  have hreprAE : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E =
      ((a0 + t * a1) * e0 + a1 * e1) • (1 : Module.End K D) +
        ((a0 + t * a1) * e1 + a1 * e0 + t * a1 * e1) • (c : Module.End K D) := by
    rw [hE1]
    exact mul_repr K hc2 (a0 + t * a1) a1 e0 e1
  have hreprCB : ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B =
      ((c0 + t * c1) * b0 + c1 * b1) • (1 : Module.End K D) +
        ((c0 + t * c1) * b1 + c1 * b0 + t * c1 * b1) • (c : Module.End K D) := by
    rw [hB1]
    exact mul_repr K hc2 (c0 + t * c1) c1 b0 b1
  have hreprSum : ((a0 + t * a1) • (1 : Module.End K D) + a1 • (c : Module.End K D)) * E +
      ((c0 + t * c1) • (1 : Module.End K D) + c1 • (c : Module.End K D)) * B =
      (((a0 + t * a1) * e0 + a1 * e1) + ((c0 + t * c1) * b0 + c1 * b1)) •
          (1 : Module.End K D) +
        (((a0 + t * a1) * e1 + a1 * e0 + t * a1 * e1) +
          ((c0 + t * c1) * b1 + c1 * b0 + t * c1 * b1)) • (c : Module.End K D) := by
    rw [hreprAE, hreprCB]
    module
  have hcomp : (((a0 + t * a1) * e0 + a1 * e1) + ((c0 + t * c1) * b0 + c1 * b1) = 1) ∧
      (((a0 + t * a1) * e1 + a1 * e0 + t * a1 * e1) +
        ((c0 + t * c1) * b1 + c1 * b0 + t * c1 * b1) = 0) := by
    have h : (((a0 + t * a1) * e0 + a1 * e1) + ((c0 + t * c1) * b0 + c1 * b1)) •
          (1 : Module.End K D) +
        (((a0 + t * a1) * e1 + a1 * e0 + t * a1 * e1) +
          ((c0 + t * c1) * b1 + c1 * b0 + t * c1 * b1)) • (c : Module.End K D) =
        (1 : K) • (1 : Module.End K D) + (0 : K) • (c : Module.End K D) := by
      rw [← hreprSum]
      simpa using hσ
    exact coeffs_eq_of_repr hd' h
  have h3a : a0 * e0 + t * a1 * e0 + a1 * e1 + c0 * b0 + t * c1 * b0 + c1 * b1 = 1 := by
    have := hcomp.1
    linear_combination this
  have h3b : a0 * e1 + a1 * e0 + c0 * b1 + c1 * b0 = 0 := by
    have hV : ((a0 + t * a1) * e1 + a1 * e0 + t * a1 * e1) +
        ((c0 + t * c1) * b1 + c1 * b0 + t * c1 * b1) =
        a0 * e1 + a1 * e0 + c0 * b1 + c1 * b0 := by
      linear_combination (t * (a1 * e1 + c1 * b1)) * (CharTwo.two_eq_zero (R := K))
    rw [hV] at hcomp
    exact hcomp.2
  have h4' : ((a0 * e0 + a1 * e1) + (b0 * c0 + b1 * c1)) • (1 : Module.End K D) +
      ((a0 * e1 + a1 * e0 + t * a1 * e1) +
        (b0 * c1 + b1 * c0 + t * b1 * c1)) • (c : Module.End K D) =
      (1 : K) • (1 : Module.End K D) + (0 : K) • (c : Module.End K D) := by
    have h := h4
    rw [hA1, hB1, hC1, hE1] at h
    rw [mul_repr K hc2 a0 a1 e0 e1, mul_repr K hc2 b0 b1 c0 c1] at h
    calc ((a0 * e0 + a1 * e1) + (b0 * c0 + b1 * c1)) • (1 : Module.End K D) +
          ((a0 * e1 + a1 * e0 + t * a1 * e1) +
            (b0 * c1 + b1 * c0 + t * b1 * c1)) • (c : Module.End K D)
        = ((a0 * e0 + a1 * e1) • (1 : Module.End K D) +
              (a0 * e1 + a1 * e0 + t * a1 * e1) • (c : Module.End K D)) +
            ((b0 * c0 + b1 * c1) • (1 : Module.End K D) +
              (b0 * c1 + b1 * c0 + t * b1 * c1) • (c : Module.End K D)) := by module
      _ = 1 := h
      _ = (1 : K) • (1 : Module.End K D) + (0 : K) • (c : Module.End K D) := by module
  have h4coeff : (a0 * e0 + a1 * e1 + b0 * c0 + b1 * c1 = 1) ∧
      (a0 * e1 + a1 * e0 + t * a1 * e1 + b0 * c1 + b1 * c0 + t * b1 * c1 = 0) := by
    have hc := coeffs_eq_of_repr hd' h4'
    exact ⟨by linear_combination hc.1, by linear_combination hc.2⟩
  have h4a : a0 * e0 + a1 * e1 + b0 * c0 + b1 * c1 = 1 := h4coeff.1
  have h4b : a0 * e1 + a1 * e0 + t * a1 * e1 + b0 * c1 + b1 * c0 + t * b1 * c1 = 0 := h4coeff.2
  obtain ⟨ha1, hb1, hc1, he1⟩ := scalar_algebra ht h1eq h2eq h3a h3b h4a h4b
  refine ⟨a0, b0, c0, e0, ?_, ?_, ?_, ?_⟩
  · simpa [ha1] using hA'
  · simpa [hb1] using hB'
  · simpa [hc1] using hC'
  · simpa [he1] using hE'


end OrthTorus

end CFSG.StandardType

end
