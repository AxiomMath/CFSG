module

public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.Permutation.SymmetricCoxeter

open Equiv Equiv.Perm

theorem normalizer_action_of_restrictions {G : Type*} [Group G] (A : Subgroup G) {k : ℕ}
    (f g : Perm (Fin (k + 3)) →* G) (t : Perm (Fin (k + 4)) →* G)
    (h1 : t.comp (viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) = f)
    (h2 : t.comp (viaEmbeddingHom (Fin.succEmb (k + 3))) = g)
    (ρ : Perm (Fin (k + 4)) →* MulAut A)
    (hf : ∀ σ, f σ ∈ Subgroup.normalizer (A : Set G))
    (hg : ∀ σ, g σ ∈ Subgroup.normalizer (A : Set G))
    (hfρ : ∀ σ, A.normalizerMonoidHom ⟨f σ, hf σ⟩ =
      ρ (viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ))
    (hgρ : ∀ σ, A.normalizerMonoidHom ⟨g σ, hg σ⟩ =
      ρ (viaEmbeddingHom (Fin.succEmb (k + 3)) σ)) :
    ∃ ht : ∀ σ, t σ ∈ Subgroup.normalizer (A : Set G),
      ∀ σ, A.normalizerMonoidHom ⟨t σ, ht σ⟩ = ρ σ := by
  have hle : t.range ≤ Subgroup.normalizer (A : Set G) := by
    rw [range_eq_sup h1 h2]
    exact sup_le (fun x hx => by
      obtain ⟨σ, rfl⟩ := hx
      exact hf σ) (fun x hx => by
      obtain ⟨σ, rfl⟩ := hx
      exact hg σ)
  let T : Perm (Fin (k + 4)) →* Subgroup.normalizer (A : Set G) :=
    t.codRestrict (Subgroup.normalizer (A : Set G)) fun x => hle ⟨x, rfl⟩
  let Tρ : Perm (Fin (k + 4)) →* MulAut A :=
    A.normalizerMonoidHom.comp T
  have hTρ : Tρ = ρ := by
    refine eq_of_comp_viaEmbeddingHom_eq k ?_ ?_
    · refine MonoidHom.ext fun σ => ?_
      change A.normalizerMonoidHom (T (viaEmbeddingHom
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)) =
        ρ (viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)
      have hσ : T (viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ) =
          ⟨f σ, hf σ⟩ := by
        refine Subtype.ext ?_
        exact congrFun (congrArg DFunLike.coe h1) σ
      rw [hσ]
      exact hfρ σ
    · refine MonoidHom.ext fun σ => ?_
      change A.normalizerMonoidHom (T (viaEmbeddingHom (Fin.succEmb (k + 3)) σ)) =
        ρ (viaEmbeddingHom (Fin.succEmb (k + 3)) σ)
      have hσ : T (viaEmbeddingHom (Fin.succEmb (k + 3)) σ) = ⟨g σ, hg σ⟩ := by
        refine Subtype.ext ?_
        exact congrFun (congrArg DFunLike.coe h2) σ
      rw [hσ]
      exact hgρ σ
  refine ⟨fun σ => hle ⟨σ, rfl⟩, ?_⟩
  intro σ
  have h := congrArg (fun φ : Perm (Fin (k + 4)) →* MulAut A => φ σ) hTρ
  simpa [Tρ, T, MonoidHom.comp_apply] using h

end CFSG.Permutation.SymmetricCoxeter
