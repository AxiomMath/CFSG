module

public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem twisted_E6_descended_root_SL2_pointwise_actors_relative_field_free {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (M : Type) [Field M] [Algebra K M] (i : Fin TwistTag.E6.tag.rank)
    (A : GL (Fin 2) M) (h : ModGL TwistTag.E6.tag M)
    (hU : ∀ B : SL2 (fixSubfield σ), h * simpleRootSL2 TwistTag.E6.tag M i (conjGL A
        (Matrix.SpecialLinearGroup.map ((algebraMap K M).comp (fixSubfield σ).subtype) B)) *
          h⁻¹ ∈ (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K M)))
    (η : MulAut (twistedE6RootGroup K σ))
    (hη : ∀ (u : twistedE6RootGroup K σ) (B : SL2 (fixSubfield σ)),
      baseChangeGL (algebraMap K M) (u : ModGL TwistTag.E6.tag K) =
        h * simpleRootSL2 TwistTag.E6.tag M i (conjGL A
          (Matrix.SpecialLinearGroup.map ((algebraMap K M).comp (fixSubfield σ).subtype) B)) *
            h⁻¹ → η u = u) :
    (Θ η = 1 ∨ Θ η = σ) ∧
    ∃ a ∈ adjointGroup TwistTag.E6.tag Ω, twistHom TwistTag.E6 Ω Fr a = a ∧
      ∃ ε : ℕ, ε < 2 ∧ ∀ u : twistedE6RootGroup K σ,
        baseChangeGL (algebraMap K Ω) (η u : ModGL TwistTag.E6.tag K) =
          a * diagramMap TwistTag.E6 Ω ^ ε * baseChangeGL (algebraMap K Ω) (u : ModGL _ K) *
            (diagramMap TwistTag.E6 Ω ^ ε)⁻¹ * a⁻¹ := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨-, -, -, -, -, hcoeΔ, -, hex, -, hPσ, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨g, u, δ, hgu⟩ := hex η
  have hΘη : Θ η = δ := hΘ η g u δ hgu
  obtain ⟨D, hD⟩ : ∃ D, rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) = D :=
    ⟨_, rfl⟩
  have hηcoe : ∀ y : twistedE6RootGroup K σ, (η y : ModGL TwistTag.E6.tag K) =
      ((g : ModGL _ K) * D) * Units.map (entrywiseHom δ.toRingHom) (y : ModGL _ K) *
        ((g : ModGL _ K) * D)⁻¹ := by
    intro y
    rw [hgu, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hcoeΔ, coe_fieldActor, hD]
    group
  have htrace : ∀ y : twistedE6RootGroup K σ,
      LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((η y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
        δ (LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) := by
    intro y
    rw [hηcoe, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
      units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
    rfl
  let _ : Algebra (fixSubfield σ) M := ((algebraMap K M).comp (fixSubfield σ).subtype).toAlgebra
  have hk : ∀ c : fixSubfield σ, δ c = c := by
    have hcl := (ordinary_E_root_SL2_full_module_traces_all_characteristics TwistTag.E6.tag
      (Or.inl rfl)).2 (fixSubfield σ) M i A h
    have hS : {x : M | ∃ B : SL2 (fixSubfield σ), x = LinearMap.trace M
        (RootModule TwistTag.E6.tag M) ((h * simpleRootSL2 TwistTag.E6.tag M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) M) B)) * h⁻¹ :
            ModGL TwistTag.E6.tag M) : Module.End M (RootModule TwistTag.E6.tag M))} ⊆
        ((fixSubfield δ).map (algebraMap K M) : Set M) := by
      rintro _ ⟨B, rfl⟩
      obtain ⟨y, hyC, hy⟩ := hU B
      have hfix : η ⟨y, hyC⟩ = ⟨y, hyC⟩ := hη ⟨y, hyC⟩ B hy
      have h1 := htrace ⟨y, hyC⟩
      rw [hfix] at h1
      refine ⟨LinearMap.trace K (RootModule TwistTag.E6.tag K)
        (y : Module.End K (RootModule TwistTag.E6.tag K)), h1.symm, ?_⟩
      change _ = LinearMap.trace M (RootModule TwistTag.E6.tag M)
        ((h * simpleRootSL2 TwistTag.E6.tag M i (conjGL A
          (Matrix.SpecialLinearGroup.map ((algebraMap K M).comp (fixSubfield σ).subtype) B)) *
            h⁻¹ : ModGL TwistTag.E6.tag M) : Module.End M (RootModule TwistTag.E6.tag M))
      rw [← hy, trace_baseChangeGL]
    have hle := Subfield.closure_le.2 hS
    rw [hcl] at hle
    intro c
    obtain ⟨y, hy, hyc⟩ := hle ⟨c, rfl⟩
    have hyc' : y = (c : K) := (algebraMap K M).injective hyc
    rw [← hyc']
    exact hy
  have hK2 : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK2
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 2 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 2 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  have hσ2 : σ ^ 2 = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσo; omega
  obtain ⟨hδdvd, hδcard⟩ := SteinbergBT.card_fixSubfield hℓ (by omega : 1 ≤ 2 * f) hK2 δ
  obtain ⟨-, hσcard⟩ := SteinbergBT.card_fixSubfield hℓ (by omega : 1 ≤ 2 * f) hK2 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  have hsub : fixSubfield σ ≤ fixSubfield δ := fun c hc => hk ⟨c, hc⟩
  have hcard_le : Nat.card (fixSubfield σ) ≤ Nat.card (fixSubfield δ) :=
    Nat.card_le_card_of_injective (fun x => (⟨x.1, hsub x.2⟩ : fixSubfield δ))
      fun x y hxy => Subtype.ext (congrArg Subtype.val hxy :)
  rw [hσcard, hδcard] at hcard_le
  have hle : f ≤ 2 * f / orderOf δ := (Nat.pow_le_pow_iff_right hℓ.one_lt).1 hcard_le
  have hδpos : 0 < orderOf δ := Nat.pos_of_dvd_of_pos hδdvd (by omega)
  have hδ2 : orderOf δ ≤ 2 := by
    by_contra hgt
    have h3 : 2 * f / orderOf δ < f :=
      (Nat.div_lt_iff_lt_mul hδpos).2 (by nlinarith)
    omega
  have hδsq : δ ^ 2 = 1 := by
    rcases (show orderOf δ = 1 ∨ orderOf δ = 2 by omega) with h1 | h1
    · rw [orderOf_eq_one_iff.1 h1, one_pow]
    · rw [← h1]
      exact pow_orderOf_eq_one δ
  have hδ : δ = 1 ∨ δ = σ := eq_one_or_eq_of_sq_eq_one hℓ hK2 hσ1 hσ2 hδsq
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left) g.2
  have hgF : twistHom TwistTag.E6 K σ.toRingHom (g : ModGL TwistTag.E6.tag K) = g :=
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom g.2).2
  have hDΩ : baseChangeGL (algebraMap K Ω) D ∈ adjointGroup TwistTag.E6.tag Ω := by
    rw [← hD, baseChangeGL_rootDiagUnit]
    exact (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag Ω _).1
  have hcomm : (algebraMap K Ω).comp σ.toRingHom = Fr.comp (algebraMap K Ω) :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hFr, ← map_pow]
      exact congrArg (algebraMap K Ω) (hσ c)
  have hDF : twistHom TwistTag.E6 K σ.toRingHom D = D :=
    hD ▸ twistHom_rootDiagUnit (compatDiag_perm u)
  have hconj : ∀ y : twistedE6RootGroup K σ,
      baseChangeGL (algebraMap K Ω) (η y : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K Ω) ((g : ModGL _ K) * D) *
          baseChangeGL (algebraMap K Ω) (Units.map (entrywiseHom δ.toRingHom)
            (y : ModGL _ K)) * (baseChangeGL (algebraMap K Ω) ((g : ModGL _ K) * D))⁻¹ := by
    intro y
    rw [hηcoe, map_mul, map_mul, map_inv]
  refine ⟨hΘη ▸ hδ, baseChangeGL (algebraMap K Ω) ((g : ModGL _ K) * D), ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ hgC) hDΩ
  · rw [twistHom_baseChangeGL (algebraMap K Ω) hcomm, map_mul, hgF, hDF]
  · rcases hδ with h1 | h1
    · refine ⟨0, by norm_num, fun y => ?_⟩
      have e1 : Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.E6.tag K) = y := by
        rw [h1]
        exact Units.ext (entrywise_id _)
      rw [hconj, e1, pow_zero, inv_one, mul_one, mul_one]
    · refine ⟨1, by norm_num, fun y => ?_⟩
      have e1 : Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.E6.tag K) =
          diagramMap TwistTag.E6 K * y * (diagramMap TwistTag.E6 K)⁻¹ := by
        rw [h1, ← hPσ y, coe_fieldActor]
      rw [hconj, e1, pow_one]
      simp only [map_mul, map_inv, baseChangeGL_diagramMap]
      group

end CFSG.RankThree.Chevalley
