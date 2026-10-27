module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.Quasithin.H13.F431.G2

open Module

variable {K : Type} [Field K]

@[expose] def bil : (K × K × K × K) →ₗ[K] (K × K × K × K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => x.1 * y.2.2.2 + y.1 * x.2.2.2 + x.2.1 * y.2.2.1 + y.2.1 * x.2.2.1)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

theorem bil_apply (x y : K × K × K × K) :
    bil x y = x.1 * y.2.2.2 + y.1 * x.2.2.2 + x.2.1 * y.2.2.1 + y.2.1 * x.2.2.1 := rfl

theorem bil_nondegenerate : (bil (K := K)).Nondegenerate := by
  constructor
  · rintro ⟨a, m, n, b⟩ h
    have h1 := h (0, 0, 0, 1)
    have h2 := h (1, 0, 0, 0)
    have h3 := h (0, 0, 1, 0)
    have h4 := h (0, 1, 0, 0)
    simp only [bil_apply] at h1 h2 h3 h4
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp_all
  · rintro ⟨a, m, n, b⟩ h
    have h1 := h (0, 0, 0, 1)
    have h2 := h (1, 0, 0, 0)
    have h3 := h (0, 0, 1, 0)
    have h4 := h (0, 1, 0, 0)
    simp only [bil_apply] at h1 h2 h3 h4
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp_all

theorem finrank_isotropic_le (W : Submodule K (K × K × K × K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, bil x y = 0) : finrank K W ≤ 2 := by
  have h1 : W ≤ LinearMap.BilinForm.orthogonal bil W := fun y hy x hx => hW x hx y hy
  have h2 := Submodule.finrank_mono h1
  rw [LinearMap.BilinForm.finrank_orthogonal bil_nondegenerate W] at h2
  have h4 : finrank K (K × K × K × K) = 4 := by simp
  omega

theorem card_isotropic_le [Finite K] (P : Set (K × K × K × K))
    (hP : ∀ x ∈ P, ∀ y ∈ P, bil x y = 0) : Nat.card P ≤ Nat.card K ^ 2 := by
  set W : Submodule K (K × K × K × K) := Submodule.span K P with hW
  have hiso : ∀ x ∈ W, ∀ y ∈ W, bil x y = 0 := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun x _ => ∀ y ∈ W, bil x y = 0) ?_ ?_ ?_ ?_ hx y hy
    · intro x hxP y hy
      refine Submodule.span_induction (p := fun y _ => bil x y = 0) ?_ ?_ ?_ ?_ hy
      · intro y hyP
        exact hP x hxP y hyP
      · simp
      · intro y z _ _ hy hz
        simp [hy, hz]
      · intro c y _ hy
        simp [hy]
    · intro y _; simp
    · intro x x' _ _ hx hx' y hy
      simp [hx y hy, hx' y hy]
    · intro c x _ hx y hy
      simp [hx y hy]
  have h1 := finrank_isotropic_le W hiso
  have h2 : Nat.card W = Nat.card K ^ finrank K W := Module.natCard_eq_pow_finrank
  have h3 : Nat.card P ≤ Nat.card W := by
    apply Nat.card_le_card_of_injective (fun x => (⟨x.1, Submodule.subset_span x.2⟩ : W))
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  calc Nat.card P ≤ Nat.card W := h3
    _ = Nat.card K ^ finrank K W := h2
    _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_right Nat.card_pos h1

end CFSG.Quasithin.H13.F431.G2
