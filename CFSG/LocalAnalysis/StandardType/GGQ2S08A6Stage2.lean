module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Stage1
public import Mathlib.LinearAlgebra.StdBasis

public section

namespace CFSG.StandardType.A6

open Matrix

private theorem a6_eq_of_basis {f g : V6 ≃ₗ[ZMod 3] V6}
    (h : ∀ i, f (e6 i) = g (e6 i)) : f = g := by
  apply LinearEquiv.ext
  have h' : (f : V6 →ₗ[ZMod 3] V6) = (g : V6 →ₗ[ZMod 3] V6) := by
    refine (Pi.basisFun (ZMod 3) (Fin 6)).ext fun i => ?_
    simpa [e6, Pi.basisFun_apply] using h i
  intro v
  exact congrArg (fun φ : V6 →ₗ[ZMod 3] V6 => φ v) h'

private theorem a6_conj_mem {M : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hW : ∀ σ, perm6 σ ∈ M) {σ : Equiv.Perm (Fin 6)} {u : V6 ≃ₗ[ZMod 3] V6}
    (h : perm6 σ * u * (perm6 σ)⁻¹ ∈ M) : u ∈ M := by
  have he : u = (perm6 σ)⁻¹ * (perm6 σ * u * (perm6 σ)⁻¹) * perm6 σ := by group
  rw [he]
  exact M.mul_mem (M.mul_mem (M.inv_mem (hW σ)) h) (hW σ)

private def a6b : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2, 3, 4, 5]

private def a6a : Equiv.Perm (Fin 6) := Equiv.swap 0 1

private def a6one : Equiv.Perm (Fin 6) := 1

private def a6c45 : Equiv.Perm (Fin 6) := List.formPerm [4, 5]

private def a6c12345 : Equiv.Perm (Fin 6) := List.formPerm [1, 2, 3, 4, 5]

private def a6c1234 : Equiv.Perm (Fin 6) := List.formPerm [1, 2, 3, 4]

private def a6c01234 : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2, 3, 4]

private theorem a6_sign6_conj (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    perm6 σ * sign6 i * (perm6 σ)⁻¹ = sign6 (σ i) := by
  rw [show sign6 i = refl6 (e6 i) (2 • e6 i) (by simp [e6, dotProduct_single]) from rfl]
  rw [show sign6 (σ i) = refl6 (e6 (σ i)) (2 • e6 (σ i))
      (by simp [e6, dotProduct_single]) from rfl]
  rw [perm6_conj_refl6]
  congr 1
  · funext j
    simp [e6, Pi.single_apply, Equiv.symm_apply_eq]
  · funext j
    simp [e6, Pi.single_apply, Equiv.symm_apply_eq]

private theorem a6_sign6_conj_inv (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    (perm6 σ)⁻¹ * sign6 i * perm6 σ = sign6 ((σ⁻¹) i) := by
  have h := a6_sign6_conj σ⁻¹ i
  simpa [perm6_inv] using h

private theorem a6_sym_false {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hA : ∀ g ∈ A, ¬ IsTransv6 g) {c a c' a' : V6} {hac : a ⬝ᵥ c = 2}
    {hac' : a' ⬝ᵥ c' = 2} (ht' : refl6 c a hac ∈ A) (hs' : refl6 c' a' hac' ∈ A)
    (h1 : a' ⬝ᵥ c = 0) (h2 : a ⬝ᵥ c' ≠ 0) : False :=
  h2 ((sym_of_noTransv hA hac hac' ht' hs').mpr h1)

private theorem a6_sym_false' {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    (hA : ∀ g ∈ A, ¬ IsTransv6 g) {c a c' a' : V6} {hac : a ⬝ᵥ c = 2}
    {hac' : a' ⬝ᵥ c' = 2} (ht' : refl6 c a hac ∈ A) (hs' : refl6 c' a' hac' ∈ A)
    (h1 : a ⬝ᵥ c' = 0) (h2 : a' ⬝ᵥ c ≠ 0) : False :=
  h2 ((sym_of_noTransv hA hac hac' ht' hs').mp h1)

private theorem a6_word1_mem {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    {r b t : V6 ≃ₗ[ZMod 3] V6} (hr : r ∈ A) (hb : b ∈ A) (ht : t ∈ A) :
    r⁻¹ * b⁻¹ * t⁻¹ ∈ A :=
  A.mul_mem (A.mul_mem (A.inv_mem hr) (A.inv_mem hb)) (A.inv_mem ht)

private theorem a6_word2_mem {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    {r b t : V6 ≃ₗ[ZMod 3] V6} (hr : r ∈ A) (hb : b ∈ A) (ht : t ∈ A) :
    r⁻¹ * t⁻¹ * r⁻¹ * b * r * b⁻¹ * r * t * r ∈ A :=
  A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem
    (A.mul_mem (A.inv_mem hr) (A.inv_mem ht)) (A.inv_mem hr)) hb) hr) (A.inv_mem hb))
    hr) ht) hr

private theorem a6_word3_mem {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    {r a b t : V6 ≃ₗ[ZMod 3] V6} (hr : r ∈ A) (hb : b ∈ A) (ha : a ∈ A) (ht : t ∈ A) :
    r * t * b⁻¹ * a⁻¹ * b * a * b⁻¹ * a * b * t * r ∈ A :=
  A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem
    (A.mul_mem (A.mul_mem (A.mul_mem hr ht) (A.inv_mem hb)) (A.inv_mem ha)) hb) ha)
    (A.inv_mem hb)) ha) hb) ht) hr

private theorem a6_word4_mem {A : Subgroup (V6 ≃ₗ[ZMod 3] V6)}
    {r t : V6 ≃ₗ[ZMod 3] V6} (hr : r ∈ A) (ht : t ∈ A) : t⁻¹ * r⁻¹ ∈ A :=
  A.mul_mem (A.inv_mem ht) (A.inv_mem hr)


theorem a6_stage2 {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (h : A6Hyp A M) {r : V6 ≃ₗ[ZMod 3] V6}
    (hr : r ∈ M) (hstd : r = rB ∨ r = rD ∨ r = rS) {t : V6 ≃ₗ[ZMod 3] V6} (ht : t ∈ A)
    (htR : IsRefl6 t) (htx : MovesLine6 t) :
    t ∈ M ∨ (r = rD ∧ ∃ i, t = sign6 i) := by
  obtain ⟨σ, c, a, hac, hsurv, hσ⟩ := a6_stage1 h ht htR htx
  have ht'A : refl6 c a hac ∈ A := by
    rw [← hσ]
    exact A.mul_mem (A.mul_mem (h.le (h.perm_mem σ)) ht)
      (A.inv_mem (h.le (h.perm_mem σ)))
  have htM_of : refl6 c a hac ∈ M → t ∈ M :=
    fun hM => a6_conj_mem h.perm_mem (hσ.symm ▸ hM)
  have hbA : perm6 a6b ∈ A := h.le (h.perm_mem _)
  have haA : perm6 a6a ∈ A := h.le (h.perm_mem _)
  simp only [a6Surv, List.mem_cons, List.mem_nil_iff, or_false] at hsurv
  rcases hstd with hstd | hstd | hstd
  · subst r
    have hrD : rD ∈ M := by
      have hid : rD = rB * perm6 a6c45 * rB := by
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem hr (h.perm_mem _)) hr
    rcases hsurv with hp | hp | hp | hp | hp | hp | hp | hp | hp
      | hp | hp | hp | hp | hp | hp | hp | hp | hp
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] hac
          = perm6 a6one * rB * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] hac
          = refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] (by decide) from rfl]
        rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c45 * rB * (perm6 a6c45)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c45)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c45)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] hac
          = perm6 a6one * rB * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] hac
          = refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] (by decide) from rfl]
        rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c45 * rB * (perm6 a6c45)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c45)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c45)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] hac
          = perm6 a6one * rD * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] hac
          = refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] (by decide) from rfl]
        rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hrD)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] hac
          = perm6 a6one * rD * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] hac
          = refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] (by decide) from rfl]
        rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hrD)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c12345 * rB * (perm6 a6c12345)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c12345)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c12345)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c12345 * rB * (perm6 a6c12345)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c12345)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c12345)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (rB)⁻¹ * (perm6 a6b)⁻¹ *
          (refl6 ![0, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 1] (by decide))⁻¹ with hH
      have ht'0 : refl6 ![0, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 1] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word1_mem (h.le hr) hbA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 1)
      have h1 : (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1)
          = e6 (τ 1) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 1) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6b * rB * (perm6 a6b)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6b)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6b)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (rB)⁻¹ * (perm6 a6b)⁻¹ *
          (refl6 ![0, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide))⁻¹ with hH
      have ht'0 : refl6 ![0, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word1_mem (h.le hr) hbA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 1)
      have h1 : (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1)
          = e6 (τ 1) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 1) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6b * rB * (perm6 a6b)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6b)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6b)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c45 * rB * (perm6 a6c45)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c45)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c45)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rB * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rB * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c12345 * rB * (perm6 a6c12345)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c12345)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c12345)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6b * rB * (perm6 a6b)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6b)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6b)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rB * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rB = refl6 (e6 5) (2 • e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
  · subst r
    rcases hsurv with hp | hp | hp | hp | hp | hp | hp | hp | hp
      | hp | hp | hp | hp | hp | hp | hp | hp | hp
    · obtain ⟨rfl, rfl⟩ := hp
      right
      refine ⟨rfl, (σ⁻¹) 5, ?_⟩
      have hsign : refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] hac = sign6 5 := by
        rw [show refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] hac
          = refl6 ![0, 0, 0, 0, 0, 1] ![0, 0, 0, 0, 0, 2] (by decide) from rfl]
        rw [show sign6 5 = refl6 (e6 5) (2 • e6 5) (by decide) from rfl]
        apply a6_eq_of_basis
        decide +kernel
      calc t = (perm6 σ)⁻¹ * (perm6 σ * t * (perm6 σ)⁻¹) * perm6 σ := by group
        _ = (perm6 σ)⁻¹ * sign6 5 * perm6 σ := by rw [hσ, hsign]
        _ = sign6 ((σ⁻¹) 5) := a6_sign6_conj_inv σ 5
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      right
      refine ⟨rfl, (σ⁻¹) 5, ?_⟩
      have hsign : refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] hac = sign6 5 := by
        rw [show refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] hac
          = refl6 ![0, 0, 0, 0, 0, 2] ![0, 0, 0, 0, 0, 1] (by decide) from rfl]
        rw [show sign6 5 = refl6 (e6 5) (2 • e6 5) (by decide) from rfl]
        apply a6_eq_of_basis
        decide +kernel
      calc t = (perm6 σ)⁻¹ * (perm6 σ * t * (perm6 σ)⁻¹) * perm6 σ := by group
        _ = (perm6 σ)⁻¹ * sign6 5 * perm6 σ := by rw [hσ, hsign]
        _ = sign6 ((σ⁻¹) 5) := a6_sign6_conj_inv σ 5
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] hac
          = perm6 a6one * rD * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] hac
          = refl6 ![0, 0, 0, 0, 1, 1] ![0, 0, 0, 0, 1, 1] (by decide) from rfl]
        rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] hac
          = perm6 a6one * rD * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] hac
          = refl6 ![0, 0, 0, 0, 2, 2] ![0, 0, 0, 0, 2, 2] (by decide) from rfl]
        rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c1234 * rD * (perm6 a6c1234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c1234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c1234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c1234 * rD * (perm6 a6c1234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c1234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c1234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (rD)⁻¹ * (refl6 ![0, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 1] (by decide))⁻¹ * (rD)⁻¹ *
          (perm6 a6b) * rD * (perm6 a6b)⁻¹ * rD *
          (refl6 ![0, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 1] (by decide)) * rD with hH
      have ht'0 : refl6 ![0, 1, 1, 1, 1, 1] ![0, 1, 1, 1, 1, 1] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word2_mem (h.le hr) hbA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 4)
      have h1 : (H * perm6 (Equiv.swap 0 4) * H⁻¹) (e6 0)
          = e6 (τ 0) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 4) * H⁻¹) (e6 0) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 0) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c01234 * rD * (perm6 a6c01234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c01234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c01234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (rD)⁻¹ * (refl6 ![0, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide))⁻¹ * (rD)⁻¹ *
          (perm6 a6b) * rD * (perm6 a6b)⁻¹ * rD *
          (refl6 ![0, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide)) * rD with hH
      have ht'0 : refl6 ![0, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word2_mem (h.le hr) hbA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 4)
      have h1 : (H * perm6 (Equiv.swap 0 4) * H⁻¹) (e6 0)
          = e6 (τ 0) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 4) * H⁻¹) (e6 0) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 0) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c01234 * rD * (perm6 a6c01234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c01234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c01234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c1234 * rD * (perm6 a6c1234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c1234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c1234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c01234 * rD * (perm6 a6c01234)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c01234)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c01234)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rD * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rD = refl6 (e6 4 + e6 5) (e6 4 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
  · subst r
    rcases hsurv with hp | hp | hp | hp | hp | hp | hp | hp | hp
      | hp | hp | hp | hp | hp | hp | hp | hp | hp
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c45 * rS * (perm6 a6c45)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c45)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c45)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 0, 1] ![1, 1, 1, 1, 1, 2] hac
          = perm6 a6one * rS * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 0, 1] ![1, 1, 1, 1, 1, 2] hac
          = refl6 ![0, 0, 0, 0, 0, 1] ![1, 1, 1, 1, 1, 2] (by decide) from rfl]
        rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6c45 * rS * (perm6 a6c45)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6c45)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6c45)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      refine Or.inl (htM_of ?_)
      have hid : refl6 ![0, 0, 0, 0, 0, 2] ![2, 2, 2, 2, 2, 1] hac
          = perm6 a6one * rS * (perm6 a6one)⁻¹ := by
        rw [show refl6 ![0, 0, 0, 0, 0, 2] ![2, 2, 2, 2, 2, 1] hac
          = refl6 ![0, 0, 0, 0, 0, 2] ![2, 2, 2, 2, 2, 1] (by decide) from rfl]
        rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
          perm6_conj_refl6]
        apply a6_eq_of_basis
        decide +kernel
      rw [hid]
      exact M.mul_mem (M.mul_mem (h.perm_mem a6one) hr)
        (M.inv_mem (h.perm_mem a6one))
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        rS * (refl6 ![0, 0, 1, 1, 1, 1] ![1, 1, 2, 2, 2, 2] (by decide)) * (perm6 a6b)⁻¹ *
          (perm6 a6a)⁻¹ * (perm6 a6b) * (perm6 a6a) * (perm6 a6b)⁻¹ * (perm6 a6a) *
          (perm6 a6b) * (refl6 ![0, 0, 1, 1, 1, 1] ![1, 1, 2, 2, 2, 2] (by decide)) * rS with hH
      have ht'0 : refl6 ![0, 0, 1, 1, 1, 1] ![1, 1, 2, 2, 2, 2] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word3_mem (h.le hr) hbA haA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 1)
      have h1 : (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 0)
          = e6 (τ 0) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 0) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 0) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        rS * (refl6 ![0, 0, 2, 2, 2, 2] ![2, 2, 1, 1, 1, 1] (by decide)) * (perm6 a6b)⁻¹ *
          (perm6 a6a)⁻¹ * (perm6 a6b) * (perm6 a6a) * (perm6 a6b)⁻¹ * (perm6 a6a) *
          (perm6 a6b) * (refl6 ![0, 0, 2, 2, 2, 2] ![2, 2, 1, 1, 1, 1] (by decide)) * rS with hH
      have ht'0 : refl6 ![0, 0, 2, 2, 2, 2] ![2, 2, 1, 1, 1, 1] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word3_mem (h.le hr) hbA haA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 1)
      have h1 : (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 0)
          = e6 (τ 0) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 0) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 0) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (refl6 ![1, 1, 1, 1, 1, 2] ![1, 1, 1, 1, 1, 0] (by decide))⁻¹ * (rS)⁻¹ with hH
      have ht'0 : refl6 ![1, 1, 1, 1, 1, 2] ![1, 1, 1, 1, 1, 0] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word4_mem (h.le hr) ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 5)
      have h1 : (H * perm6 (Equiv.swap 0 5) * H⁻¹) (e6 1)
          = e6 (τ 1) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 5) * H⁻¹) (e6 1) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 1) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false h.noTransv ht'A hsA (by decide) (by decide)
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      set H : V6 ≃ₗ[ZMod 3] V6 :=
        (rS)⁻¹ * (perm6 a6b)⁻¹ *
          (refl6 ![1, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide))⁻¹ with hH
      have ht'0 : refl6 ![1, 2, 2, 2, 2, 2] ![0, 2, 2, 2, 2, 2] (by decide) ∈ A := ht'A
      have hHA : H ∈ A := by
        rw [hH]
        exact a6_word1_mem (h.le hr) hbA ht'0
      have hfix : FixesLine6 H := by
        rw [hH]
        change H one6 = one6 ∨ H one6 = -one6
        decide +kernel
      obtain ⟨τ, hτ⟩ := h.normW H hHA hfix (Equiv.swap 0 1)
      have h1 : (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1)
          = e6 (τ 1) := by
        rw [hτ, perm6_e6]
      have h2 : ∀ m : Fin 6,
          (H * perm6 (Equiv.swap 0 1) * H⁻¹) (e6 1) ≠ e6 m := by
        rw [hH]
        decide +kernel
      exact h2 (τ 1) h1
    · obtain ⟨rfl, rfl⟩ := hp
      exfalso
      have hsA :
          perm6 a6one * rS * (perm6 a6one)⁻¹ ∈ A := by
        exact A.mul_mem (A.mul_mem (h.le (h.perm_mem a6one)) (h.le hr))
          (A.inv_mem (h.le (h.perm_mem a6one)))
      rw [show rS = refl6 (e6 5) (one6 + e6 5) (by decide) from rfl,
        perm6_conj_refl6] at hsA
      exact a6_sym_false' h.noTransv ht'A hsA (by decide) (by decide)

end CFSG.StandardType.A6

end
