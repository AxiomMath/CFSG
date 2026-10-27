module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityRoots

public section

namespace CFSG.StandardType

namespace Triality

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame
open scoped commutatorElement

theorem three_le_four : 3 ≤ 4 := by norm_num

abbrev Sp8 (K : Type) [Field K] : Type := spinGroup (quadPlus 4 K)

variable {K : Type} [Field K]

noncomputable abbrev xr (γ : Fin 4 → ℤ) (c : K) : Sp8 K :=
  SpinPlus.x 4 K three_le_four γ c

noncomputable abbrev Φ8 (K : Type) [Field K] : RootSystem (Fin 4) := SpinPlus.Φ 4 K three_le_four

theorem Φ8_roots : (Φ8 K).roots = rootsD4 := rfl

theorem xr_add {γ : Fin 4 → ℤ} (c d : K) : xr γ (c + d) = xr γ c * xr γ d :=
  rootElt_add _ _ c d

theorem intCast_eq_one_of_natAbs [CharP K 2] {z : ℤ} (hz : z.natAbs = 1) : (z : K) = 1 := by
  rcases Int.natAbs_eq_iff.1 hz with rfl | rfl <;> simp [CharTwo.neg_eq]

theorem intCast_commC [CharP K 2] (α β : Fin 4 → ℤ) (p : ℕ × ℕ) :
    (SpinPlus.commC α β p : K) = 1 :=
  intCast_eq_one_of_natAbs (SpinPlus.commC_natAbs α β p)

theorem lift_chevOf {G : Type*} [Group G] (f : ChevGen (Φ8 K) K → G) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (Φ8 K).roots) (c : K) :
    FreeGroup.lift f (chevOf (Φ := Φ8 K) γ c) = f (⟨γ, hγ⟩, c) := by
  rw [chevOf, dite_eq_left hγ, FreeGroup.lift_apply_of]

noncomputable abbrev triGen (g : ChevGen (Φ8 K) K) : Sp8 K := xr (tri g.1.1) g.2

theorem tri_add_ne_zero {α β : Fin 4 → ℤ} (h : α + β ≠ 0) : tri α + tri β ≠ 0 := by
  rw [← map_add]
  intro h'
  exact h (tri_injective (h'.trans (map_zero tri).symm))

theorem tri_rels [CharP K 2] (O : CommOrder (Φ8 K)) :
    ∀ r ∈ relA (Φ8 K) K ∪ relB (Φ8 K) K O SpinPlus.commC,
      FreeGroup.lift (triGen (K := K)) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · rw [map_mul, map_mul, map_inv, lift_chevOf _ hγ, lift_chevOf _ hγ, lift_chevOf _ hγ, triGen,
      triGen, triGen, xr_add, mul_inv_cancel]
  · have htα : tri α ∈ (Φ8 K).roots := tri_mem_roots hα
    have htβ : tri β ∈ (Φ8 K).roots := tri_mem_roots hβ
    have htαβ := tri_add_ne_zero hαβ
    have hcomm := SpinPlus.commutatorFormula three_le_four O (tri α) htα (tri β) htβ htαβ c d
    by_cases hr : α + β ∈ (Φ8 K).roots
    · have hr' : tri α + tri β ∈ (Φ8 K).roots := by
        rw [← map_add]
        exact tri_mem_roots hr
      rw [(SpinPlus.commOrder_list_eq three_le_four O hα hβ hαβ).1 hr]
      rw [(SpinPlus.commOrder_list_eq three_le_four O htα htβ htαβ).1 hr'] at hcomm
      simp only [List.map_singleton, List.prod_singleton, one_smul, pow_one] at hcomm ⊢
      rw [map_mul, map_commutatorElement, map_inv, lift_chevOf _ hα, lift_chevOf _ hβ,
        lift_chevOf _ hr, triGen, triGen, triGen, hcomm, intCast_commC, intCast_commC,
        map_add, mul_inv_cancel]
    · have hr' : tri α + tri β ∉ (Φ8 K).roots := by
        rw [← map_add]
        exact fun h => hr (tri_mem_roots_iff.1 h)
      rw [(SpinPlus.commOrder_list_eq three_le_four O hα hβ hαβ).2 hr]
      rw [(SpinPlus.commOrder_list_eq three_le_four O htα htβ htαβ).2 hr'] at hcomm
      simp only [List.map_nil, List.prod_nil, inv_one, mul_one] at hcomm ⊢
      rw [map_commutatorElement, lift_chevOf _ hα, lift_chevOf _ hβ, triGen, triGen, hcomm]

theorem ext_xr {G : Type*} [Group G] {f g : Sp8 K →* G}
    (h : ∀ γ ∈ rootsD4, ∀ c : K, f (xr γ c) = g (xr γ c)) : f = g := by
  have hle : ⨆ γ ∈ rootsD4, plusRootGroup 4 K three_le_four γ ≤ MonoidHom.eqLocus f g := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization three_le_four γ hγ).1 z).1 hz
    exact h γ hγ c
  rw [plusDatum_iSup_eq_top 4 K three_le_four] at hle
  exact MonoidHom.ext fun z => hle (Subgroup.mem_top z)

section Presentation

variable [Finite K]

noncomputable def ord8 (K : Type) [Field K] [Finite K] : CommOrder (Φ8 K) :=
  (SpinPlus.conclusionB (K := K) three_le_four).2.1.some

theorem pres_rels (O : CommOrder (Φ8 K)) :
    ∀ r ∈ relA (Φ8 K) K ∪ relB (Φ8 K) K O SpinPlus.commC,
      FreeGroup.lift (chevEval (SpinPlus.x 4 K three_le_four)) r = 1 :=
  ((SpinPlus.presentationB three_le_four O).2 SpinPlus.commC
    (SpinPlus.commutatorFormula three_le_four O)).fst

theorem pres_bijective (O : CommOrder (Φ8 K)) :
    Function.Bijective (PresentedGroup.toGroup (pres_rels O)) :=
  ((SpinPlus.presentationB three_le_four O).2 SpinPlus.commC
    (SpinPlus.commutatorFormula three_le_four O)).snd

@[expose] noncomputable def presEquiv (O : CommOrder (Φ8 K)) :
    PresentedGroup (relA (Φ8 K) K ∪ relB (Φ8 K) K O SpinPlus.commC) ≃* Sp8 K :=
  MulEquiv.ofBijective (PresentedGroup.toGroup (pres_rels O)) (pres_bijective O)

theorem presEquiv_of (O : CommOrder (Φ8 K)) {γ : Fin 4 → ℤ} (hγ : γ ∈ (Φ8 K).roots) (c : K) :
    presEquiv O (PresentedGroup.of (⟨γ, hγ⟩, c)) = xr γ c := by
  rw [presEquiv, MulEquiv.ofBijective_apply]
  exact PresentedGroup.toGroup.of (pres_rels O)

variable [CharP K 2]

@[expose] noncomputable def triSpin : Sp8 K →* Sp8 K :=
  (PresentedGroup.toGroup (tri_rels (ord8 K))).comp (presEquiv (ord8 K)).symm.toMonoidHom

theorem triSpin_xr {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    triSpin (xr γ c) = xr (tri γ) c := by
  have hγ' : γ ∈ (Φ8 K).roots := hγ
  have h : (presEquiv (ord8 K)).symm (xr γ c) = PresentedGroup.of (⟨γ, hγ'⟩, c) := by
    rw [MulEquiv.symm_apply_eq, presEquiv_of]
  rw [triSpin, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  exact PresentedGroup.toGroup.of (tri_rels (ord8 K))

theorem triSpin_cube (z : Sp8 K) : triSpin (triSpin (triSpin z)) = z := by
  have h : triSpin.comp (triSpin.comp triSpin) = MonoidHom.id (Sp8 K) := by
    refine ext_xr fun γ hγ c => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, triSpin_xr hγ, triSpin_xr (tri_mem_roots hγ),
      triSpin_xr (tri_mem_roots (tri_mem_roots hγ)), tri_tri_tri, MonoidHom.id_apply]
  exact DFunLike.congr_fun h z

@[expose] noncomputable def triSpinAut : MulAut (Sp8 K) where
  toFun := triSpin
  invFun z := triSpin (triSpin z)
  left_inv z := triSpin_cube z
  right_inv z := triSpin_cube z
  map_mul' := map_mul triSpin

theorem triSpinAut_apply (z : Sp8 K) : triSpinAut z = triSpin z := rfl

theorem triSpinAut_xr {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) (c : K) :
    triSpinAut (xr γ c) = xr (tri γ) c :=
  triSpin_xr hγ c

theorem triSpinAut_cube : (triSpinAut : MulAut (Sp8 K)) ^ 3 = 1 := by
  refine MulEquiv.ext fun z => ?_
  rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
  exact triSpin_cube z

end Presentation

end Triality

end CFSG.StandardType
