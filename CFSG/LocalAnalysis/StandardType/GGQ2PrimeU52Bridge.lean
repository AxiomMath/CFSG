module

public import CFSG.Models

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models

theorem outThree_of_equiv {R M : Type*} [Group R] [Group M] (e : R ≃* M)
    (h : ∀ φ : MulAut M, φ ^ 3 = 1 → ∃ r, φ = MulAut.conj r) :
    ∀ φ : MulAut R, φ ^ 3 = 1 → ∃ r, φ = MulAut.conj r := by
  intro φ hφ
  let ψ : MulAut M := (e.symm.trans φ).trans e
  have hψ : ψ ^ 3 = 1 := by
    ext m
    have := congrArg (fun χ : MulAut R => χ (e.symm m)) hφ
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at this
    simp [ψ, pow_succ, MulAut.mul_apply, this]
  obtain ⟨m₀, hm₀⟩ := h ψ hψ
  refine ⟨e.symm m₀, ?_⟩
  ext x
  have := congrArg (fun χ : MulAut M => χ (e x)) hm₀
  simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
  rw [MulAut.conj_apply]
  apply e.injective
  rw [this]
  simp

@[expose] def conjAut {G : Type*} [Group G]
    (L : Subgroup G) {b : G} (hb : b ∈ normalizer (L : Set G)) : MulAut L where
  toFun t := ⟨b * t * b⁻¹, (mem_normalizer_iff.1 hb t).1 t.2⟩
  invFun t := ⟨b⁻¹ * t * b, by simpa using (mem_normalizer_iff.1 (inv_mem hb) t).1 t.2⟩
  left_inv t := by ext; simp [mul_assoc]
  right_inv t := by ext; simp [mul_assoc]
  map_mul' s t := by ext; simp [mul_assoc]

@[expose] def U52OrderThreeAutInner : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 →
    ∀ φ : MulAut (StatedProj (StatedSU 5 (2 ^ 1) K)), φ ^ 3 = 1 → ∃ r, φ = MulAut.conj r

theorem lieModel_PSU_five {R : Type} [Group R] (h : LieModel R .PSU 5 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 ∧
      Nonempty (R ≃* StatedProj (StatedSU 5 (2 ^ 1) K)) := by
  rcases h.2 with h | ⟨h, -⟩
  · exact h.2
  · exact absurd h (by norm_num)

end CFSG.GGQ2Prime
