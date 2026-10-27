module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E7
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E8
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem P10a_cover_E7
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* TableBExc.RecipeGroup .E7 F) :
    Subgroup.center K = ⊥ ∧ ∃ eK : K ≃* adjointGroup .E7 F,
      (∀ k : K, eK k = TableBExc.recipeEquiv .E7 F (θ (QuotientGroup.mk k))) ∧
      ∀ φ ∈ TableBExc.RecipeID .E7 F, ∃ k₀ : K, ∀ k : K,
        φ (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (k₀ * k * k₀⁻¹)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP F 2 := charP_two_of_card (K := F) (m := 1) (by rw [pow_one]; exact hF)
  let ψ : K →* TableBExc.RecipeGroup .E7 F :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center K := by
    rw [show ψ.ker = (QuotientGroup.mk' (Subgroup.center K)).ker from
      MonoidHom.ker_comp_of_injective _ θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']
  have hbot : ψ.ker = ⊥ :=
    CFSG.StandardType.SmallExc.ker_eq_bot_recipe_E7_two hF K ψ hψ hker hperf
  have hZ : Subgroup.center K = ⊥ := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center K),
      ← MonoidHom.ker_comp_of_injective _ θ.toMonoidHom θ.injective]
    exact hbot
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
  let eK : K ≃* adjointGroup .E7 F :=
    (MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩).trans (TableBExc.recipeEquiv .E7 F)
  refine ⟨hZ, eK, ?_, ?_⟩
  · intro k
    rfl
  · intro φ hφ
    obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_E7 F hφ
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    refine ⟨k₀, fun k => ?_⟩
    rw [← hr, ← hq, ← hk₀]
    change (MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center K) k₀)))
        (θ (QuotientGroup.mk' (Subgroup.center K) k)) =
      θ (QuotientGroup.mk' (Subgroup.center K) (k₀ * k * k₀⁻¹))
    calc MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center K) k₀))
          (θ (QuotientGroup.mk' (Subgroup.center K) k))
        = θ (QuotientGroup.mk' (Subgroup.center K) k₀) *
            θ (QuotientGroup.mk' (Subgroup.center K) k) *
            (θ (QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹ := MulAut.conj_apply _ _
      _ = θ ((QuotientGroup.mk' (Subgroup.center K) k₀) *
              (QuotientGroup.mk' (Subgroup.center K) k)) *
            θ (((QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹) := by
          rw [← map_mul, ← map_inv]
      _ = θ (((QuotientGroup.mk' (Subgroup.center K) k₀) *
              (QuotientGroup.mk' (Subgroup.center K) k)) *
            ((QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹) := by
          rw [← map_mul]
      _ = θ (QuotientGroup.mk' (Subgroup.center K) (k₀ * k * k₀⁻¹)) := by
          congr 1

theorem P10a_cover_E8
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* TableBExc.RecipeGroup .E8 F) :
    Subgroup.center K = ⊥ ∧ ∃ eK : K ≃* adjointGroup .E8 F,
      (∀ k : K, eK k = TableBExc.recipeEquiv .E8 F (θ (QuotientGroup.mk k))) ∧
      ∀ φ ∈ TableBExc.RecipeID .E8 F, ∃ k₀ : K, ∀ k : K,
        φ (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (k₀ * k * k₀⁻¹)) := by
  let ψ : K →* TableBExc.RecipeGroup .E8 F :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center K := by
    rw [show ψ.ker = (QuotientGroup.mk' (Subgroup.center K)).ker from
      MonoidHom.ker_comp_of_injective _ θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']
  have hbot : ψ.ker = ⊥ :=
    CFSG.StandardType.SmallExc.ker_eq_bot_recipe_E8_two hF K ψ hψ hker hperf
  have hZ : Subgroup.center K = ⊥ := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center K),
      ← MonoidHom.ker_comp_of_injective _ θ.toMonoidHom θ.injective]
    exact hbot
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
  let eK : K ≃* adjointGroup .E8 F :=
    (MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩).trans (TableBExc.recipeEquiv .E8 F)
  refine ⟨hZ, eK, ?_, ?_⟩
  · intro k
    rfl
  · intro φ hφ
    obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_E8 F hφ
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    refine ⟨k₀, fun k => ?_⟩
    rw [← hr, ← hq, ← hk₀]
    change (MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center K) k₀)))
        (θ (QuotientGroup.mk' (Subgroup.center K) k)) =
      θ (QuotientGroup.mk' (Subgroup.center K) (k₀ * k * k₀⁻¹))
    calc MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center K) k₀))
          (θ (QuotientGroup.mk' (Subgroup.center K) k))
        = θ (QuotientGroup.mk' (Subgroup.center K) k₀) *
            θ (QuotientGroup.mk' (Subgroup.center K) k) *
            (θ (QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹ := MulAut.conj_apply _ _
      _ = θ ((QuotientGroup.mk' (Subgroup.center K) k₀) *
              (QuotientGroup.mk' (Subgroup.center K) k)) *
            θ (((QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹) := by
          rw [← map_mul, ← map_inv]
      _ = θ (((QuotientGroup.mk' (Subgroup.center K) k₀) *
              (QuotientGroup.mk' (Subgroup.center K) k)) *
            ((QuotientGroup.mk' (Subgroup.center K) k₀))⁻¹) := by
          rw [← map_mul]
      _ = θ (QuotientGroup.mk' (Subgroup.center K) (k₀ * k * k₀⁻¹)) := by
          congr 1

end CFSG.StandardType.FrameRoute
