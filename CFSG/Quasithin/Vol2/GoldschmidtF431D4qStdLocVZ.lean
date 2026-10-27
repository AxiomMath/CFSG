module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocWeyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem hm_mem_cent_tC (μ : (trialityFixedField K σ.toRingHom)ˣ) :
    (⟨trialityMiddleTorus K σ μ, trialityMiddleTorus_mem_d4C σ hσ μ⟩ : Cm σ) ∈
      Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  show trialityMiddleTorus K σ μ * d4x₄ K σ 1 = d4x₄ K σ 1 * trialityMiddleTorus K σ μ
  exact mul_inv_eq_iff_eq_mul.1 (hm_conj_d4x₄ σ μ 1)

include hσ in
theorem naC_mem_cent_tC : naC σ ∈ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) :=
  Subgroup.mem_centralizer_singleton_iff.2 (naC_commute_tC σ hσ)

include hσ in
theorem x2_mem_cent_tC {β : K} (hβ : σ β = β) :
    (⟨d4x₂ K β, (d4x_long_mem σ hβ).1⟩ : Cm σ) ∈
      Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  show d4x₂ K β * d4x₄ K σ 1 = d4x₄ K σ 1 * d4x₂ K β
  exact (d4Ma_commute_d4x₄ σ _ (d4x₂_mem_d4Ma σ hβ) 1).symm

include hσ in
theorem VaC_conj_z : ∀ v ∈ VaC σ, v ≠ 1 →
    ∃ x ∈ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)), v = x * zC σ * x⁻¹ := by
  intro v hv hv1
  obtain ⟨e, f, he, hf, hve⟩ := exists_coord_of_mem_VaC σ hσ hv
  by_cases he0 : e = 0
  · subst he0
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hv1 (Subtype.ext (hve.trans (d4v_zero σ)))
    let μ : (trialityFixedField K σ.toRingHom)ˣ :=
      Units.mk0 ⟨f, (mem_trialityFixedField).2 hf⟩ (fun h => hf0 (congrArg Subtype.val h))
    refine ⟨⟨trialityMiddleTorus K σ μ, trialityMiddleTorus_mem_d4C σ hσ μ⟩,
      hm_mem_cent_tC σ hσ μ, Subtype.ext ?_⟩
    rw [hve]
    show d4v K σ 0 0 0 0 f = trialityMiddleTorus K σ μ * d4x₆ K 1 * (trialityMiddleTorus K σ μ)⁻¹
    rw [hm_conj_d4x₆ σ μ 1, d4x₆_eq_d4v σ]
    exact d4v_congr σ rfl rfl rfl rfl (by
      have hμ : ((trialityFixedUnit K σ μ : Kˣ) : K) = f := rfl
      rw [hμ, mul_one])
  · have hβ : σ (f / e) = f / e := by rw [map_div₀, hf, he]
    let μ : (trialityFixedField K σ.toRingHom)ˣ :=
      Units.mk0 ⟨e, (mem_trialityFixedField).2 he⟩ (fun h => he0 (congrArg Subtype.val h))
    refine ⟨⟨d4x₂ K (f / e), (d4x_long_mem σ hβ).1⟩ * naC σ *
      ⟨trialityMiddleTorus K σ μ, trialityMiddleTorus_mem_d4C σ hσ μ⟩,
      mul_mem (mul_mem (x2_mem_cent_tC σ hσ hβ) (naC_mem_cent_tC σ hσ))
        (hm_mem_cent_tC σ hσ μ), Subtype.ext ?_⟩
    rw [hve]
    have h1 : trialityMiddleTorus K σ μ * d4x₆ K 1 * (trialityMiddleTorus K σ μ)⁻¹ =
        d4x₆ K e := by
      rw [hm_conj_d4x₆ σ μ 1]
      have hμ : ((trialityFixedUnit K σ μ : Kˣ) : K) = e := rfl
      rw [hμ, mul_one]
    have h2 : trialityMiddleRep K * d4x₆ K e * (trialityMiddleRep K)⁻¹ = d4x₅ K e :=
      trialityMiddleRep_conj_d4x₆ e
    have h3 : d4x₂ K (f / e) * d4x₅ K e * (d4x₂ K (f / e))⁻¹ = d4v K σ 0 0 0 e f := by
      rw [d4x₅_eq_d4v σ, d4x₂_conj_d4v σ hσ (f / e) 0 0 0 e 0]
      exact d4v_congr σ rfl rfl rfl rfl (by rw [add_zero]; field_simp)
    show d4v K σ 0 0 0 e f = (d4x₂ K (f / e) * trialityMiddleRep K * trialityMiddleTorus K σ μ) *
      d4x₆ K 1 * (d4x₂ K (f / e) * trialityMiddleRep K * trialityMiddleTorus K σ μ)⁻¹
    calc d4v K σ 0 0 0 e f = d4x₂ K (f / e) * d4x₅ K e * (d4x₂ K (f / e))⁻¹ := h3.symm
      _ = d4x₂ K (f / e) * (trialityMiddleRep K * d4x₆ K e * (trialityMiddleRep K)⁻¹) *
          (d4x₂ K (f / e))⁻¹ := by rw [h2]
      _ = d4x₂ K (f / e) * (trialityMiddleRep K * (trialityMiddleTorus K σ μ * d4x₆ K 1 *
          (trialityMiddleTorus K σ μ)⁻¹) * (trialityMiddleRep K)⁻¹) * (d4x₂ K (f / e))⁻¹ := by
        rw [h1]
      _ = _ := by group

end CFSG.Quasithin.H13.F431.D4q.StdLoc
