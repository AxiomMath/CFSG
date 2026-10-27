module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCent

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique
  CFSG.Quasithin

set_option linter.unusedSectionVars false

section Centre

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4v_mem_graphFixedPosUnipotent {b c d e f : K} (hb : σ b = b) (he : σ e = e)
    (hf : σ f = f) : d4v K σ b c d e f ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
  graphFixedSimpleComplement_le _ (d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) hb he hf)

include hσ in
theorem centre_Ust {u : Cm σ} (hu : u ∈ Ust σ) (hc : ∀ v ∈ Ust σ, u * v = v * u) :
    ∃ f : K, σ f = f ∧ (u : ModGL TwistTag.D4.tag K) = d4x₆ K f := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  have hcw0 : ∀ {x : ModGL TwistTag.D4.tag K},
      x ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom → (u : ModGL TwistTag.D4.tag K) * x =
        x * u := fun {x} hx =>
    congrArg Subtype.val (hc ⟨x, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hx⟩
      (Subgroup.mem_subgroupOf.mpr hx))
  obtain ⟨a, b, c, d, e, f, hb, he, hf, hu'⟩ :=
    exists_d4coord σ hσ3 (Subgroup.mem_subgroupOf.mp hu)
  have hcw : ∀ {x : ModGL TwistTag.D4.tag K},
      x ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom →
      d4x₁ K σ a * d4v K σ b c d e f * x = x * (d4x₁ K σ a * d4v K σ b c d e f) := fun {x} hx => by
    rw [← hu']
    exact hcw0 hx
  have hx4 : ∀ δ : K, d4x₄ K σ δ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := fun δ => by
    rw [d4x₄_eq_d4v σ]
    exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_zero σ) (map_zero σ)
  have h4 : ∀ δ : K, (a * δ + σ (a * δ) + σ (σ (a * δ))) = 0 ∧
      (δ * c + σ (δ * c) + σ (σ (δ * c))) = 0 := fun δ => by
    have h := conj_eq_of_commute_d4 (hcw (hx4 δ))
    rw [coord_conj_d4x₄ σ hσ, d4x₄_eq_d4v σ] at h
    have h' := d4v_injective σ h
    exact ⟨h'.2.2.2.1, h'.2.2.2.2⟩
  have ha : a = 0 := eq_zero_of_trace_d4 σ fun δ => (h4 δ).1
  have hc0 : c = 0 := eq_zero_of_trace_d4 σ fun δ => by rw [mul_comm]; exact (h4 δ).2
  subst ha hc0
  simp only [d4x₁_zero, one_mul] at hcw hu'
  have h5 := hcw (by
    rw [d4x₅_eq_d4v σ]
    exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_one σ) (map_zero σ) :
      d4x₅ K 1 ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
  rw [d4x₅_eq_d4v σ] at h5
  have hb0 := d4v_commute_imp σ hσ h5
  simp only [mul_zero, map_zero, add_zero, zero_add, one_mul] at hb0
  have h2 := hcw (by
    rw [d4x₂_eq_d4v σ]
    exact d4v_mem_graphFixedPosUnipotent σ hσ (map_one σ) (map_zero σ) (map_zero σ) :
      d4x₂ K 1 ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
  rw [d4x₂_eq_d4v σ] at h2
  have he0 := d4v_commute_imp σ hσ h2
  simp only [mul_zero, zero_mul, map_zero, add_zero, zero_add, mul_one] at he0
  have hd0 : d = 0 := eq_zero_of_trace_d4 σ fun γ => by
    have h := hcw (by
      rw [d4x₃_eq_d4v σ]
      exact d4v_mem_graphFixedPosUnipotent σ hσ (map_zero σ) (map_zero σ) (map_zero σ) :
        d4x₃ K σ γ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    rw [d4x₃_eq_d4v σ] at h
    have h' := d4v_commute_imp σ hσ h
    simpa using h'
  exact ⟨f, hf, by rw [hu', d4x₆_eq_d4v σ, ← hb0, hd0, he0]⟩

include hσ in
theorem trialityMiddleTorus_mem_graphFixedRootTorus
    (β : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ β ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    even_triality_faithful_torus_coordinates K σ (ringEquiv_cube_d4 σ hσ)
  have h1 := (e (1, β)).2
  have h0 : trialityOuterTorus K σ 1 = 1 := by
    simp only [trialityOuterTorus, map_one, torusElt_one, List.map_const', List.prod_replicate,
      one_pow]
  rw [he, h0, one_mul] at h1
  exact h1

include hσ in
theorem exists_torus_zC {f : K} (hf : σ f = f) (hf0 : f ≠ 0) :
    ∃ h : Cm σ, h ∈ Pst0 σ ∧ h ∈ Pst1 σ ∧
      ((h * zC σ * h⁻¹ : Cm σ) : ModGL TwistTag.D4.tag K) = d4x₆ K f := by
  have hfk : f ∈ trialityFixedField K σ.toRingHom := (mem_trialityFixedField).2 hf
  let μ : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨f, hfk⟩ (fun h => hf0 (congrArg Subtype.val h))
  have hmC := trialityMiddleTorus_mem_d4C σ hσ μ
  have hB : trialityMiddleTorus K σ μ ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    graphFixedRootTorus_le_graphFixedRootBorel (trialityMiddleTorus_mem_graphFixedRootTorus σ hσ μ)
  refine ⟨⟨trialityMiddleTorus K σ μ, hmC⟩, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hB)
  · exact Subgroup.mem_subgroupOf.mpr
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _ hB)
  · show trialityMiddleTorus K σ μ * d4x₆ K 1 * (trialityMiddleTorus K σ μ)⁻¹ = d4x₆ K f
    have hμ : ((trialityFixedUnit K σ μ : Kˣ) : K) = f := rfl
    rw [d4x₆_eq_d4v σ, hm_conj_d4v σ μ 0 0 0 0 1, d4x₆_eq_d4v σ, hμ]
    exact d4v_congr σ (by simp) (by simp) rfl (by simp) (by simp)

theorem conj_mem_autStab_of_mem {G : Type} [Group G] {P : Subgroup G} {h : G} (hh : h ∈ P) :
    MulAut.conj h ∈ autStab P := by
  have := conj_mul_mem_autStab hh (ψ := (1 : MulAut G)) (fun _ => Iff.rfl)
  simpa using this

variable (Kb : Subgroup (MulAut (Cm σ)))
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

end Centre

end CFSG.Quasithin.H13.F431.D4q.Loc
