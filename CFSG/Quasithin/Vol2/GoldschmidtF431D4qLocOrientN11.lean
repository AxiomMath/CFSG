module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrientCoord
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrientRoot

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false


section ConjZ

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_conj_zC_of_V {x : Cm σ} {e f : K} (he : σ e = e) (hf : σ f = f)
    (hx : (x : ModGL TwistTag.D4.tag K) = d4v K σ 0 0 0 e f) (hx1 : x ≠ 1) :
    ∃ c : Cm σ, c * zC σ * c⁻¹ = x := by
  by_cases he0 : e = 0
  · subst he0
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hx1 (Subtype.ext (by rw [hx]; exact d4v_zero σ))
    obtain ⟨h, -, -, hh⟩ := exists_torus_zC σ hσ hf hf0
    exact ⟨h, Subtype.ext (by rw [hh, hx, ← d4x₆_eq_d4v σ])⟩
  · have hβ : σ (f / e) = f / e := by rw [map_div₀, he, hf]
    obtain ⟨h, -, -, hh⟩ := exists_torus_zC σ hσ he he0
    have hw1 : ((x2C σ (f / e) hβ * x * (x2C σ (f / e) hβ)⁻¹ : Cm σ) :
        ModGL TwistTag.D4.tag K) = d4x₅ K e := by
      show d4x₂ K (f / e) * (x : ModGL TwistTag.D4.tag K) * (d4x₂ K (f / e))⁻¹ = d4x₅ K e
      have h1 : d4x₂ K (f / e) * d4v K σ 0 0 0 e f = d4v K σ (f / e) 0 0 e f := by
        simp only [d4v, d4x₂_zero, d4x₃_zero, d4x₄_zero, one_mul, mul_one, mul_assoc]
      have h2 : e * (f / e) = f := by field_simp
      rw [hx, d4x₂_inv K (f / e), h1, d4v_mul_d4x₂ σ, d4x₅_eq_d4v σ]
      refine d4v_congr σ (CharTwo.add_self_eq_zero _) rfl rfl rfl ?_
      rw [h2]
      exact CharTwo.add_self_eq_zero f
    have hw2 : ((naC σ * (x2C σ (f / e) hβ * x * (x2C σ (f / e) hβ)⁻¹) * (naC σ)⁻¹ : Cm σ) :
        ModGL TwistTag.D4.tag K) = d4x₆ K e := by
      show trialityMiddleRep K * ((x2C σ (f / e) hβ * x * (x2C σ (f / e) hβ)⁻¹ : Cm σ) :
        ModGL TwistTag.D4.tag K) * (trialityMiddleRep K)⁻¹ = d4x₆ K e
      rw [hw1]
      exact trialityMiddleRep_conj_d4x₅ e
    have key : naC σ * (x2C σ (f / e) hβ * x * (x2C σ (f / e) hβ)⁻¹) * (naC σ)⁻¹ =
        h * zC σ * h⁻¹ := Subtype.ext (by rw [hw2, hh])
    refine ⟨(naC σ * x2C σ (f / e) hβ)⁻¹ * h, ?_⟩
    calc ((naC σ * x2C σ (f / e) hβ)⁻¹ * h) * zC σ * ((naC σ * x2C σ (f / e) hβ)⁻¹ * h)⁻¹
        = (naC σ * x2C σ (f / e) hβ)⁻¹ * (h * zC σ * h⁻¹) * (naC σ * x2C σ (f / e) hβ) := by
          group
      _ = (naC σ * x2C σ (f / e) hβ)⁻¹ * (naC σ * (x2C σ (f / e) hβ * x *
          (x2C σ (f / e) hβ)⁻¹) * (naC σ)⁻¹) * (naC σ * x2C σ (f / e) hβ) := by rw [key]
      _ = x := by group

end ConjZ

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem not_cent_mod_Z {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) :
    ∃ s ∈ Ust σ, ⁅s, φ (tC σ hσ)⁆ ∉ ZC σ := by
  by_contra H
  push Not at H
  have hxQ : φ (tC σ hσ) ∈ QC σ := aut_QC σ hf hK hσq hφ (tC_mem_QC σ hσ)
  obtain ⟨e, f', he, hf', hx⟩ := exists_coord_of_cent_mod_Z σ hσ hf hK hσq hxQ H
  have hx1 : φ (tC σ hσ) ≠ 1 := fun h => tC_ne_one σ hσ (φ.injective (by rw [h, map_one]))
  obtain ⟨c, hc⟩ := exists_conj_zC_of_V σ hσ he hf' hx hx1
  apply no_aut_zC_tC σ hσ (φ⁻¹ * MulAut.conj c)
  rw [MulAut.mul_apply, MulAut.conj_apply, hc]
  exact MulAut.inv_apply_self _ φ _

end Main

end CFSG.Quasithin.H13.F431.D4q.Loc
