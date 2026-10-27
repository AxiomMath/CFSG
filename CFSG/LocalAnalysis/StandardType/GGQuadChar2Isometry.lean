module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType.QuadChar2

open QuadraticMap

variable {F E : Type*} [Field F] [CharP F 2] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
variable {Q : QuadraticForm F E}

private lemma map_add_smul (x y : E) (c : F) :
    Q (x + c • y) = Q x + c ^ 2 * Q y + c * polar Q x y := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, polar_smul_right]
  simp only [smul_eq_mul]
  ring

private lemma polar_map {g : E ≃ₗ[F] E} (hg : ∀ x, Q (g x) = Q x) (x y : E) :
    polar Q (g x) (g y) = polar Q x y := by
  have h1 : Q (g x + g y) = Q (g x) + Q (g y) + polar Q (g x) (g y) := by
    rw [QuadraticMap.map_add Q]
  have h2 : Q (g x + g y) = Q x + Q y + polar Q x y := by
    rw [← map_add g x y, hg, QuadraticMap.map_add Q]
  rw [h1, hg x, hg y] at h2
  exact add_left_cancel h2

private lemma eq_self_of_polar_eq_zero {u : E} (hu : Q u = 1)
    {g : E ≃ₗ[F] E} (hg : ∀ x, Q (g x) = Q x)
    (htriv : ∀ x, polar Q x u = 0 → g x - x ∈ Submodule.span F {u})
    {x : E} (hx : polar Q x u = 0) : g x = x := by
  obtain ⟨f, hf⟩ := Submodule.mem_span_singleton.mp (htriv x hx)
  have hgx : g x = x + f • u := by
    rw [hf]
    abel
  have hQval : Q (g x) = Q x + f ^ 2 := by
    rw [hgx, map_add_smul, hu, hx]
    ring
  have hf2 : f ^ 2 = 0 := by
    have h := hg x
    rw [hQval] at h
    exact add_left_cancel (a := Q x) (b := f ^ 2) (c := 0) (by simpa using h)
  have hf0 : f = 0 := sq_eq_zero_iff.mp hf2
  rw [hgx, hf0, zero_smul, add_zero]

private lemma sub_mem_span (hQ : (polarBilin Q).Nondegenerate) {u : E} (hu : Q u = 1)
    {g : E ≃ₗ[F] E} (hg : ∀ x, Q (g x) = Q x)
    (htriv : ∀ x, polar Q x u = 0 → g x - x ∈ Submodule.span F {u}) (y : E) :
    g y - y ∈ Submodule.span F {u} := by
  let B : LinearMap.BilinForm F E := polarBilin Q
  have hBapp : ∀ a b : E, B a b = polar Q a b := fun a b =>
    QuadraticMap.polarBilin_apply_apply Q a b
  have hQB : B.Nondegenerate := hQ
  have hsymm : B.IsSymm := LinearMap.BilinForm.IsSymm.mk fun a b => by
    rw [hBapp, hBapp, polar_comm]
  rw [← LinearMap.BilinForm.orthogonal_orthogonal (B := B) hQB hsymm.isRefl
    (Submodule.span F {u})]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro z hz
  have hzu : B u z = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hz) u (Submodule.subset_span (Set.mem_singleton u))
  have hzu' : polar Q u z = 0 := by rw [← hBapp]; exact hzu
  have hz_u : polar Q z u = 0 := by rw [polar_comm]; exact hzu'
  have hgz : g z = z := eq_self_of_polar_eq_zero hu hg htriv hz_u
  have e1 : polar Q z (g y) = polar Q z y := by
    conv_lhs => rw [← hgz]
    exact polar_map hg z y
  show B z (g y - y) = 0
  rw [hBapp]
  calc polar Q z (g y - y) = polar Q z (g y) + polar Q z (-y) := by
        rw [sub_eq_add_neg, polar_add_right]
    _ = polar Q z (g y) - polar Q z y := by rw [polar_neg_right, sub_eq_add_neg]
    _ = polar Q z y - polar Q z y := by rw [e1]
    _ = 0 := sub_self _

private lemma exists_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {u : E} (hu : Q u = 1) :
    ∃ y : E, polar Q y u = 1 := by
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  let B : LinearMap.BilinForm F E := polarBilin Q
  have hBapp : ∀ a b : E, B a b = polar Q a b := fun a b =>
    QuadraticMap.polarBilin_apply_apply Q a b
  have hQB : B.Nondegenerate := hQ
  have hsymm : B.IsSymm := LinearMap.BilinForm.IsSymm.mk fun a b => by
    rw [hBapp, hBapp, polar_comm]
  have hy : ∃ y, B y u ≠ 0 := by
    by_contra h
    have h' : ∀ y, B y u = 0 := by
      intro y
      by_contra hy
      exact h ⟨y, hy⟩
    have hBu : B u = 0 := by
      ext x
      rw [LinearMap.zero_apply, hsymm.eq u x]
      exact h' x
    have hker : u ∈ LinearMap.ker B := by rwa [LinearMap.mem_ker]
    rw [hQB.ker_eq_bot] at hker
    exact hu_ne (by simpa using hker)
  obtain ⟨y, hy⟩ := hy
  refine ⟨(B y u)⁻¹ • y, ?_⟩
  rw [polar_smul_left, ← hBapp y u, smul_eq_mul, inv_mul_cancel₀ hy]

theorem isometry_eq_one_or_transvection
    {F E : Type*} [Field F] [CharP F 2] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    {Q : QuadraticForm F E} (hQ : (polarBilin Q).Nondegenerate)
    {u : E} (hu : Q u = 1) {g : E ≃ₗ[F] E} (hg : ∀ x, Q (g x) = Q x)
    (htriv : ∀ x, polar Q x u = 0 → g x - x ∈ Submodule.span F {u}) :
    g = 1 ∨ ∀ x, g x = x + polar Q x u • u := by
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  let B : LinearMap.BilinForm F E := polarBilin Q
  have hBapp : ∀ a b : E, B a b = polar Q a b := fun a b =>
    QuadraticMap.polarBilin_apply_apply Q a b
  have hspan : ∀ y, g y - y ∈ Submodule.span F {u} := fun y =>
    sub_mem_span hQ hu hg htriv y
  let T : E →ₗ[F] Submodule.span F {u} :=
    (g.toLinearMap - LinearMap.id).codRestrict (Submodule.span F {u}) (fun y => by
      simpa using hspan y)
  let coord : Submodule.span F {u} ≃ₗ[F] F := LinearEquiv.coord F E u hu_ne
  let c : E →ₗ[F] F := coord.toLinearMap.comp T
  have hc : ∀ y, c y • u = g y - y := by
    intro y
    have h := LinearEquiv.coord_apply_smul F E u hu_ne (T y)
    simpa [c, coord, T, LinearMap.codRestrict_apply, LinearMap.sub_apply] using h
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one hQ hu
  have hB0 : B y₀ u = 1 := by rw [hBapp, hy₀]
  have hker : ∀ x, polar Q x u = 0 → c x = 0 := by
    intro x hx
    have h1 : c x • u = 0 := by
      rw [hc x, eq_self_of_polar_eq_zero hu hg htriv hx, sub_self]
    exact smul_left_injective F hu_ne (h1.trans (zero_smul F u).symm)
  have hrel : ∀ y, c y = B y u * c y₀ := by
    intro y
    have hmem : polar Q (y - B y u • y₀) u = 0 := by
      rw [polar_sub_left, polar_smul_left, ← hBapp y u, ← hBapp y₀ u, hB0, smul_eq_mul,
        mul_one, sub_self]
    have hczero : c (y - B y u • y₀) = 0 := hker _ hmem
    have hlin : c (y - B y u • y₀) = c y - B y u * c y₀ := by
      rw [map_sub, map_smul, smul_eq_mul]
    exact sub_eq_zero.mp (by rw [← hlin]; exact hczero)
  have hQgy : ∀ y, Q (g y) = Q y + (c y) ^ 2 * Q u + c y * polar Q y u := by
    intro y
    have hgy : g y = y + c y • u := by
      rw [hc y]
      abel
    rw [hgy, map_add_smul]
  have heq : ∀ y, (c y) ^ 2 + c y * (B y u) = 0 := by
    intro y
    have h := hg y
    rw [hQgy y, hu, ← hBapp y u, mul_one] at h
    have h' : Q y + ((c y) ^ 2 + c y * (B y u)) = Q y + 0 := by
      rw [← add_assoc]
      simpa using h
    exact add_left_cancel h'
  have hc0 : c y₀ = 0 ∨ c y₀ = 1 := by
    have hsq : (c y₀) ^ 2 + c y₀ = 0 := by
      have h := heq y₀
      rw [hB0] at h
      simpa using h
    have hfac : c y₀ * (c y₀ + 1) = 0 := by
      rw [← hsq]
      ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl h
    · right
      have : c y₀ = -1 := eq_neg_of_add_eq_zero_left h
      simpa [CharTwo.neg_eq] using this
  rcases hc0 with h0 | h1
  · left
    refine LinearEquiv.ext fun y => ?_
    have hy : c y = 0 := by rw [hrel y, h0, mul_zero]
    have hgy := hc y
    rw [hy, zero_smul] at hgy
    exact sub_eq_zero.mp hgy.symm
  · right
    intro y
    have hy : c y = B y u := by rw [hrel y, h1, mul_one]
    have hgy := hc y
    rw [hy, hBapp y u] at hgy
    rw [hgy]
    abel

end CFSG.StandardType.QuadChar2
