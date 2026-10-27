module

public import Mathlib.GroupTheory.Perm.ViaEmbedding

public section

namespace CFSG.Permutation

open Equiv Equiv.Perm

theorem viaEmbeddingHom_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (ι : α ↪ β)
    (i j : α) : viaEmbeddingHom ι (swap i j) = swap (ι i) (ι j) := by
  ext x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y, rfl⟩ := hx
    rw [viaEmbeddingHom_apply, viaEmbedding_apply, ι.injective.swap_apply]
  · rw [viaEmbeddingHom_apply, viaEmbedding_apply_of_notMem _ _ _ hx, swap_apply_of_ne_of_ne]
    · rintro rfl
      exact hx ⟨i, rfl⟩
    · rintro rfl
      exact hx ⟨j, rfl⟩

theorem viaEmbeddingHom_trans_equiv {α β γ : Type*} (ι : α ↪ β) (e : β ≃ γ)
    (σ : Equiv.Perm α) :
    viaEmbeddingHom (ι.trans e.toEmbedding) σ =
      e.permCongr (viaEmbeddingHom ι σ) := by
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.Perm.viaEmbeddingHom_apply,
    Equiv.Perm.viaEmbeddingHom_apply]
  by_cases hy : y ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hy
    have h := Equiv.Perm.viaEmbedding_apply σ (ι.trans e.toEmbedding) a
    rw [Function.Embedding.trans_apply, Equiv.coe_toEmbedding] at h
    rw [h, Equiv.Perm.viaEmbedding_apply]
    rfl
  · have hy' : e y ∉ Set.range (ι.trans e.toEmbedding) := by
      rintro ⟨a, ha⟩
      rw [Function.Embedding.trans_apply, Equiv.coe_toEmbedding] at ha
      exact hy ⟨a, e.injective ha⟩
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem σ _ _ hy',
      Equiv.Perm.viaEmbedding_apply_of_notMem σ ι y hy]

theorem viaEmbeddingHom_trans_conj {α β : Type*} (q : Equiv.Perm β) (e : α ↪ β)
    (τ : Equiv.Perm α) :
    viaEmbeddingHom (e.trans q.toEmbedding) τ = q * viaEmbeddingHom e τ * q⁻¹ := by
  rw [viaEmbeddingHom_trans_equiv e q τ, Equiv.permCongr_eq_mul]

end CFSG.Permutation
