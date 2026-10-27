module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

public section

namespace CFSG.StandardType

private theorem l02qj1_pow_bijective (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) :
    Function.Bijective (fun i : Fin 3 => σ ^ (i : ℕ)) := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  have : FiniteDimensional k K := Module.Finite.of_finite
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hσ]; exact i.isLt)
    (by rw [Set.mem_Iio, hσ]; exact j.isLt) hij), ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdeg]

theorem kgLangT3_hilbert90 (k K : Type) [Field k] [Field K] [Algebra k K] [Finite K]
    (hdeg : Module.finrank k K = 3) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3) (ζ : kˣ)
    (hζ : ζ ^ 3 = 1) :
    ∃ c : Kˣ, Units.mapEquiv σ.toRingEquiv.toMulEquiv c =
      Units.map (algebraMap k K).toMonoidHom ζ * c := by
  have : Finite k := Finite.of_injective _ (algebraMap k K).injective
  have : FiniteDimensional k K := Module.Finite.of_finite
  have hgen : ∀ τ : K ≃ₐ[k] K, τ ∈ Subgroup.zpowers σ := by
    intro τ
    obtain ⟨i, rfl⟩ := (l02qj1_pow_bijective k K hdeg σ hσ).2 τ
    exact Subgroup.pow_mem (Subgroup.zpowers σ) (Subgroup.mem_zpowers σ) i
  have hnorm : Algebra.norm k ((algebraMap k K) (ζ : k)) = 1 := by
    rw [Algebra.norm_algebraMap, hdeg]
    have h : ((ζ : kˣ) : k) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    exact h
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (K := k) (L := K) (g := σ) hgen
    (x := (algebraMap k K) (ζ : k)) hnorm
  have hyU : y * (Units.mapEquiv σ.toRingEquiv.toMulEquiv y)⁻¹ =
      Units.map (algebraMap k K).toMonoidHom ζ := by
    apply Units.ext
    simp only [Units.coe_mapEquiv, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val,
      MonoidHom.coe_coe]
    change (y : K) * (σ (y : K))⁻¹ = (algebraMap k K) (ζ : k)
    rw [div_eq_mul_inv] at hy
    exact hy
  have hσinv : (Units.mapEquiv σ.toRingEquiv.toMulEquiv y)⁻¹ =
      y⁻¹ * Units.map (algebraMap k K).toMonoidHom ζ := by
    rw [← hyU, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨y⁻¹, ?_⟩
  rw [map_inv, hσinv, mul_comm]

end CFSG.StandardType
