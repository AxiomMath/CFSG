module

public import CFSG.Quasithin.Background.G118Inputs
public import CFSG.Quasithin.Background.P3GL24Red
public import CFSG.Quasithin.Background.P3GL24Geom

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open scoped LinearAlgebra.Projectivization
open Equiv

section

variable {F : Type} [Field F] {U : Type} [AddCommGroup U] [Module F U]

theorem gl24_main [Finite F] [Module.Finite F U] (hF : Nat.card F = 4)
    (hU : Module.finrank F U = 2) (C : Subgroup (U ≃ₗ[F] U)) {τ : F ≃+* F}
    (σ : U →ₛₗ[(τ : F →+* F)] U) (hσ : Function.Bijective σ) (hτ : τ ≠ RingEquiv.refl F)
    (hinv : ∀ p : ℙ F U, Projectivization.map σ hσ.1 (Projectivization.map σ hσ.1 p) = p)
    (hnorm : ∀ c ∈ C, ∃ c' ∈ C, ∀ u : U, c' (σ u) = σ (c u))
    (hO2 : ∀ N : Subgroup ↥C, N.Normal → IsPGroup 2 N → N = ⊥)
    (hy : ∃ y ∈ C, y ≠ 1 ∧ y * y = 1) :
    ((∀ c ∈ C, (∃ a : F, ∀ u : U, c u = a • u) → c = 1) ∧
        (Nonempty (↥C ≃* Perm (Fin 3)) ∨ Nonempty (↥C ≃* ↥(alternatingGroup (Fin 5))))) ∨
      (∃ ζ ∈ C, ζ ≠ 1 ∧ (∃ a : F, ∀ u : U, ζ u = a • u) ∧
        ∃ c ∈ C, c * c * c = 1 ∧ ¬ ∃ a : F, ∀ u : U, c u = a • u) := by
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have : Finite U := Module.finite_of_finite F
  obtain ⟨e⟩ : Nonempty (ℙ F U ≃ Fin 5) :=
    ⟨Finite.equivFinOfCardEq (gl24_card_proj hF hU)⟩
  have hker : ∀ g : U ≃ₗ[F] U, g ∈ (gl24Rho5 e).ker ↔ ∃ a : F, ∀ u : U, g u = a • u := by
    intro g
    rw [MonoidHom.mem_ker, gl24Rho5_eq_one_iff, gl24Rho_eq_one_iff]
  have hs2 : e.permCongrHom (gl24Sigma σ hσ.1 hinv) * e.permCongrHom (gl24Sigma σ hσ.1 hinv) =
      1 := by
    rw [← map_mul, gl24Sigma_mul_self, map_one]
  have hsodd : Perm.sign (e.permCongrHom (gl24Sigma σ hσ.1 hinv)) = -1 :=
    gl24_sigma_sign hF hU e σ hσ.1 hinv hτ
  have hs : ∀ c ∈ C, ∃ c' ∈ C, gl24Rho5 e c' =
      e.permCongrHom (gl24Sigma σ hσ.1 hinv) * gl24Rho5 e c *
        (e.permCongrHom (gl24Sigma σ hσ.1 hinv))⁻¹ := by
    intro c hc
    obtain ⟨c', hc', h⟩ := hnorm c hc
    refine ⟨c', hc', ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    have := gl24Sigma_conj σ hσ.1 hinv c c' h
    simp only [gl24Rho5, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, this]
  have hred := gl24_reduction (gl24Rho5 e)
    (fun z hz g => gl24_ker_central z ((hker z).1 hz).choose ((hker z).1 hz).choose_spec g)
    (fun z hz => gl24_ker_pow_three hF z ((gl24Rho5_eq_one_iff e z).1 hz))
    (fun g hg => gl24_cube hF hU g ((gl24Rho5_eq_one_iff e _).1 hg))
    (gl24Rho5_sign hF hU e)
    (e.permCongrHom (gl24Sigma σ hσ.1 hinv)) hs2 hsodd C hs hO2 hy
  rcases hred with ⟨h1, h2⟩ | ⟨ζ, hζ, hζ1, hζk, c, hc, hc3, hck⟩
  · exact Or.inl ⟨fun c hc hsc => h1 c hc ((hker c).2 hsc), h2⟩
  · exact Or.inr ⟨ζ, hζ, hζ1, (hker ζ).1 hζk, c, hc, hc3, fun h => hck ((hker c).2 h)⟩

end

theorem gl24SubInput : GL24SubInput := by
  intro F _ _ U _ _ _ hF hU C τ σ hσ hτ hinv hnorm hO2 hy
  rcases gl24_main hF hU C σ hσ hτ hinv hnorm hO2 hy with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨fun c hc hsc => h1 c hc hsc, h2⟩
  · exact Or.inr h

end G118

end G11

end CFSG.Quasithin
