module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley

private abbrev E1 : Fin TwistTag.E6.tag.rank → ℤ := (Pi.single (0 : Fin 6) 1 : Fin 6 → ℤ)

private abbrev E6 : Fin TwistTag.E6.tag.rank → ℤ := (Pi.single (5 : Fin 6) 1 : Fin 6 → ℤ)

private theorem permLattice_E1 : permLattice TwistTag.E6.perm E1 = E6 := by
  decide +kernel

private theorem iform_E1_E6 :
    CFSG.LieType.Steinberg.Adjoint.iform (τ := TwistTag.E6.tag) E1 E6 = 0 := by
  decide +kernel

private theorem not_isRoot_E1_E6 :
    ¬ IsRoot TwistTag.E6.tag (E1 + E6) := by
  intro h
  have h' := (CFSG.LieType.Chevalley.RootOps.isRootB_iff (τ := TwistTag.E6.tag)).2 h
  rw [show CFSG.LieType.Chevalley.RootOps.isRootB TwistTag.E6.tag (E1 + E6) = false by
    decide +kernel] at h'
  exact Bool.false_ne_true h'

private theorem iform_highest_E6 :
    CFSG.LieType.Steinberg.Adjoint.iform (τ := TwistTag.E6.tag)
      CFSG.LieType.Chevalley.e6HighestRoot E6 = 0 := by
  decide +kernel

private theorem not_isRoot_highest_E6 :
    ¬ IsRoot TwistTag.E6.tag (CFSG.LieType.Chevalley.e6HighestRoot + E6) := by
  intro h
  have h' := (CFSG.LieType.Chevalley.RootOps.isRootB_iff (τ := TwistTag.E6.tag)).2 h
  rw [show CFSG.LieType.Chevalley.RootOps.isRootB TwistTag.E6.tag
    (CFSG.LieType.Chevalley.e6HighestRoot + E6) = false by decide +kernel] at h'
  exact Bool.false_ne_true h'

variable {K : Type} [Field K]

private theorem units_map_entrywiseHom_pinnedX_E6
    (σ : K →+* K)
    (α : Fin TwistTag.E6.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ) (pinnedX TwistTag.E6.tag K α c) =
      pinnedX TwistTag.E6.tag K α (σ c) :=
  Units.ext (CFSG.LieType.Chevalley.entrywise_pinnedX σ α c)

private theorem map_inv_mul_of_conj_eq {G : Type*} [Group G] (ψ α β : MulAut G)
    (h : ψ * α * ψ⁻¹ = β) (u : G) :
    ψ ((α (ψ.symm u))⁻¹ * ψ.symm u) = (β u)⁻¹ * u := by
  have h' : ψ * α = β * ψ := by rw [← h]; group
  have h1 : ψ (α (ψ.symm u)) = β u := by
    have := congrArg (fun f : MulAut G => f (ψ.symm u)) h'
    simpa [MulAut.mul_apply] using this
  rw [map_mul, map_inv, h1, MulEquiv.apply_symm_apply]


private theorem rootOne_mul_rootSix (c d : K) :
    pinnedX TwistTag.E6.tag K E1 c * pinnedX TwistTag.E6.tag K E6 d =
      pinnedX TwistTag.E6.tag K E6 d * pinnedX TwistTag.E6.tag K E1 c :=
  CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K
    (isRoot_single TwistTag.E6.tag ⟨0, by decide⟩)
    (isRoot_single TwistTag.E6.tag ⟨5, by decide⟩) iform_E1_E6 not_isRoot_E1_E6 c d

private theorem rootSix_mul_rootOne (c d : K) :
    pinnedX TwistTag.E6.tag K E6 c * pinnedX TwistTag.E6.tag K E1 d =
      pinnedX TwistTag.E6.tag K E1 d * pinnedX TwistTag.E6.tag K E6 c :=
  (rootOne_mul_rootSix d c).symm

private theorem highest_mul_rootSix (d : K) :
    pinnedX TwistTag.E6.tag K CFSG.LieType.Chevalley.e6HighestRoot 1 *
        pinnedX TwistTag.E6.tag K E6 d =
      pinnedX TwistTag.E6.tag K E6 d *
        pinnedX TwistTag.E6.tag K CFSG.LieType.Chevalley.e6HighestRoot 1 :=
  CFSG.LieType.Chevalley.pinnedX_commute_of_iform_eq_zero K
    CFSG.LieType.Chevalley.isRoot_e6HighestRoot
    (isRoot_single TwistTag.E6.tag ⟨5, by decide⟩) iform_highest_E6 not_isRoot_highest_E6 1 d

private noncomputable abbrev rootOne (c : K) : adjointGroup TwistTag.E6.tag K :=
  ⟨pinnedX TwistTag.E6.tag K E1 c, pinnedX_mem_adjointGroup E1 c⟩

private noncomputable abbrev rootSix (c : K) : adjointGroup TwistTag.E6.tag K :=
  ⟨pinnedX TwistTag.E6.tag K E6 c, pinnedX_mem_adjointGroup E6 c⟩

private theorem exists_frame_of_single (α β₀ φ : MulAut (adjointGroup TwistTag.E6.tag K))
    (hφ : φ * α * φ⁻¹ = β₀) {e : K} (he : e ≠ 0)
    (hβu : (β₀ (rootOne (K := K) 1) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K E6 e) :
    ∃ (ψ : MulAut (adjointGroup TwistTag.E6.tag K))
      (x : adjointGroup TwistTag.E6.tag K) (d₁ d₆ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K E1 (d₁ : K) * pinnedX TwistTag.E6.tag K E6 (d₆ : K) := by
  refine ⟨φ, φ.symm (rootOne (K := K) 1), 1, Units.mk0 (-e) (neg_ne_zero.2 he), ?_⟩
  rw [map_inv_mul_of_conj_eq φ α β₀ hφ]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hβu, pinnedX_neg]
  exact (rootOne_mul_rootSix 1 (-e)).symm

private theorem exists_frame_of_field (α β₀ φ : MulAut (adjointGroup TwistTag.E6.tag K))
    (hφ : φ * α * φ⁻¹ = β₀) {σ : K ≃+* K} {c : K} (hc : σ c ≠ c)
    (hβu : (β₀ (rootOne (K := K) c * rootSix (K := K) c) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K E1 (σ c) * pinnedX TwistTag.E6.tag K E6 (σ c)) :
    ∃ (ψ : MulAut (adjointGroup TwistTag.E6.tag K))
      (x : adjointGroup TwistTag.E6.tag K) (d₁ d₆ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K E1 (d₁ : K) * pinnedX TwistTag.E6.tag K E6 (d₆ : K) := by
  have hne : c - σ c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
  refine ⟨φ, φ.symm (rootOne (K := K) c * rootSix (K := K) c),
    Units.mk0 (c - σ c) hne, Units.mk0 (c - σ c) hne, ?_⟩
  rw [map_inv_mul_of_conj_eq φ α β₀ hφ]
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hβu]
  rw [show ((rootOne (K := K) c * rootSix (K := K) c : adjointGroup TwistTag.E6.tag K) :
    ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K E1 c *
      pinnedX TwistTag.E6.tag K E6 c from rfl]
  have h1 : (pinnedX TwistTag.E6.tag K E1 (σ c))⁻¹ =
      pinnedX TwistTag.E6.tag K E1 (-(σ c)) := pinnedX_neg TwistTag.E6.tag K E1 (σ c)
  have h2 : (pinnedX TwistTag.E6.tag K E6 (σ c))⁻¹ =
      pinnedX TwistTag.E6.tag K E6 (-(σ c)) := pinnedX_neg TwistTag.E6.tag K E6 (σ c)
  calc (pinnedX TwistTag.E6.tag K E1 (σ c) * pinnedX TwistTag.E6.tag K E6 (σ c))⁻¹ *
        (pinnedX TwistTag.E6.tag K E1 c * pinnedX TwistTag.E6.tag K E6 c)
      = pinnedX TwistTag.E6.tag K E6 (-(σ c)) * pinnedX TwistTag.E6.tag K E1 (-(σ c)) *
          (pinnedX TwistTag.E6.tag K E1 c * pinnedX TwistTag.E6.tag K E6 c) := by
        rw [mul_inv_rev, h1, h2]
    _ = pinnedX TwistTag.E6.tag K E6 (-(σ c)) *
          (pinnedX TwistTag.E6.tag K E1 (-(σ c)) * pinnedX TwistTag.E6.tag K E1 c) *
          pinnedX TwistTag.E6.tag K E6 c := by
        group
    _ = pinnedX TwistTag.E6.tag K E6 (-(σ c)) *
          pinnedX TwistTag.E6.tag K E1 (-(σ c) + c) * pinnedX TwistTag.E6.tag K E6 c := by
        rw [← pinnedX_add]
    _ = pinnedX TwistTag.E6.tag K E1 (-(σ c) + c) *
          pinnedX TwistTag.E6.tag K E6 (-(σ c)) * pinnedX TwistTag.E6.tag K E6 c := by
        rw [rootSix_mul_rootOne]
    _ = pinnedX TwistTag.E6.tag K E1 (-(σ c) + c) *
          (pinnedX TwistTag.E6.tag K E6 (-(σ c)) * pinnedX TwistTag.E6.tag K E6 c) := by
        group
    _ = pinnedX TwistTag.E6.tag K E1 (-(σ c) + c) *
          pinnedX TwistTag.E6.tag K E6 (-(σ c) + c) := by
        rw [← pinnedX_add]
    _ = pinnedX TwistTag.E6.tag K E1 (c - σ c) *
          pinnedX TwistTag.E6.tag K E6 (c - σ c) := by
        rw [show -(σ c) + c = c - σ c by ring]


private theorem exists_frame_aux {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup TwistTag.E6.tag K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup TwistTag.E6.tag K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup TwistTag.E6.tag K)) (x : adjointGroup TwistTag.E6.tag K)
      (d₁ d₆ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K E1 (d₁ : K) * pinnedX TwistTag.E6.tag K E6 (d₆ : K) := by
  classical
  have hα : α ^ 2 = 1 := by rw [pow_two]; exact h2
  have hαo : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup TwistTag.E6.tag K) := by
    rintro ⟨c, hc⟩
    exact hout c hc.symm
  obtain ⟨ε, hε, hεc⟩ :=
    CFSG.LieType.Chevalley.diagramMap_conj_pinnedX (t := TwistTag.E6) (K := K) (α := E1)
      (isRoot_single TwistTag.E6.tag ⟨0, by decide⟩)
  have he : ε ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hε
    exact zero_ne_one hε
  rcases CFSG.SeitzReduction.E6Pilot.outer_involution_cases_E6 hf K hK α hα hαo with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨ht, φ, hφ⟩⟩ | ⟨σ, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  ·
    refine exists_frame_of_single α η φ hφ he ?_
    rw [hη]
    rw [show (↑(rootOne (K := K) 1) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K E1 1 from rfl]
    rw [hεc 1, permLattice_E1, mul_one]
  ·
    have het : (η (rootOne (K := K) 1) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K E6 ε := by
      rw [hη]
      rw [show (↑(rootOne (K := K) 1) : ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K E1 1 from rfl]
      rw [hεc 1, permLattice_E1, mul_one]
    set β₀ : MulAut (adjointGroup TwistTag.E6.tag K) :=
      MulAut.conj ⟨pinnedX TwistTag.E6.tag K CFSG.LieType.Chevalley.e6HighestRoot 1, ht⟩ * η
      with hβ₀def
    refine exists_frame_of_single α β₀ φ (hφ.trans hβ₀def.symm) he ?_
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [het]
    rw [highest_mul_rootSix]
    group
  ·
    obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
      by_contra h
      exact hσ1 (RingEquiv.ext fun x => not_not.1 (not_exists.1 h x))
    refine exists_frame_of_field α
      (CFSG.LieType.Chevalley.entrywiseAdjointAut TwistTag.E6.tag σ) φ hφ hc ?_
    rw [CFSG.LieType.Chevalley.coe_entrywiseAdjointAut]
    rw [show (↑(rootOne (K := K) c * rootSix (K := K) c) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K E1 c * pinnedX TwistTag.E6.tag K E6 c from rfl]
    rw [map_mul, units_map_entrywiseHom_pinnedX_E6 σ.toRingHom E1 c,
      units_map_entrywiseHom_pinnedX_E6 σ.toRingHom E6 c]
    rfl
  ·
    refine exists_frame_of_single α
      (CFSG.LieType.Chevalley.diagramConjAut TwistTag.E6 K *
        CFSG.LieType.Chevalley.entrywiseAdjointAut TwistTag.E6.tag σ) φ hφ he ?_
    rw [MulAut.mul_apply, CFSG.LieType.Chevalley.coe_diagramConjAut,
      CFSG.LieType.Chevalley.coe_entrywiseAdjointAut]
    rw [show (↑(rootOne (K := K) 1) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K E1 1 from rfl]
    rw [units_map_entrywiseHom_pinnedX_E6 σ.toRingHom E1 1,
      show σ.toRingHom 1 = 1 from map_one σ.toRingHom]
    rw [hεc 1, permLattice_E1, mul_one]

theorem e6_exists_inv_mul_eq_frame {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup .E6 K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup .E6 K, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut (adjointGroup .E6 K)) (x : adjointGroup .E6 K) (d₁ d₆ : Kˣ),
      ((ψ ((α x)⁻¹ * x) : adjointGroup .E6 K) : ModGL .E6 K) =
        pinnedX .E6 K (Pi.single (0 : Fin 6) 1) (d₁ : K) *
          pinnedX .E6 K (Pi.single (5 : Fin 6) 1) (d₆ : K) :=
  exists_frame_aux hf hK α h2 hout

end CFSG.LocalAnalysis.WeakClosure81
