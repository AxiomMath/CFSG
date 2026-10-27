module

public import CFSG.Monster.B.Fischer.HexadCode
public import CFSG.Monster.B.TwoA.Fischer.CliqueM22Design
public import CFSG.Monster.B.TwoA.Fischer.SplitAffine

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Coord

variable {C : Set V} [Finite C] (η : C ≃ X₀)

@[expose] def cliqueCoordEquiv : (C →₀ ZMod 2) ≃ₗ[ZMod 2] V₀ :=
  (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) C).trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) η.symm)

theorem cliqueCoordEquiv_apply (w : C →₀ ZMod 2) (i : X₀) :
    cliqueCoordEquiv η w i = w (η.symm i) := rfl

theorem cliqueCoordEquiv_single (z : C) : cliqueCoordEquiv η (Finsupp.single z 1) = e (η z) := by
  classical
  funext i
  rw [cliqueCoordEquiv_apply, e]
  by_cases h : i = η z
  · subst h
    simp
  · have h' : z ≠ η.symm i := fun h' => h (by rw [h', Equiv.apply_symm_apply])
    simp [h, h']

theorem cliqueCoordEquiv_mapDomain {σ : Equiv.Perm C} {τ : Equiv.Perm X₀}
    (h : ∀ z, η (σ z) = τ (η z)) (w : C →₀ ZMod 2) :
    cliqueCoordEquiv η (Finsupp.mapDomain σ w) = permRep τ (cliqueCoordEquiv η w) := by
  funext i
  rw [cliqueCoordEquiv_apply, Finsupp.mapDomain_equiv_apply, permRep_apply, cliqueCoordEquiv_apply]
  congr 1
  rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[expose] def cliqueCoordQuot : (C →₀ ZMod 2) →ₗ[ZMod 2] W₀ :=
  K₀.mkQ ∘ₗ (cliqueCoordEquiv η).toLinearMap

theorem cliqueCoordQuot_apply (w : C →₀ ZMod 2) :
    cliqueCoordQuot η w = K₀.mkQ (cliqueCoordEquiv η w) := rfl

theorem cliqueCoordQuot_surjective : Function.Surjective (cliqueCoordQuot η) :=
  (Submodule.mkQ_surjective K₀).comp (cliqueCoordEquiv η).surjective

end Coord

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

section Code

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Finite C] (η : C ≃ X₀)
  (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22)

omit hS in
theorem E₀_le_map_cliqueCode
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) :
    E₀ ≤ (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap := by
  classical
  have : Fintype C := Fintype.ofFinite C
  rw [E₀, Submodule.span_le]
  rintro _ ⟨B₀, hB₀, rfl⟩
  have hB₀X := (block_spec hB₀).1
  set T : Finset C := Finset.univ.filter fun z => (η z : Fin 24) ∈ B₀ with hT
  have hTB : T.image (fun z => (η z : Fin 24)) = B₀ := by
    ext i
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (Finset.mem_filter.1 hz).2
    · intro hi
      refine ⟨η.symm ⟨i, hB₀X hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [Equiv.apply_symm_apply]
        exact hi
      · rw [Equiv.apply_symm_apply]
  obtain ⟨T', hT'0, -, hTT'⟩ := (mem_cliqueBlocks_iff _).1 ((hη T).2 (by rw [hTB]; exact hB₀))
  rw [← image_val_injective hTT'] at hT'0
  have hw : indicWord T ∈ cliqueCode lab C := by
    rw [mem_cliqueCode_iff, support_indicWord]
    exact hT'0
  refine ⟨indicWord T, hw, funext fun i => ?_⟩
  show cliqueCoordEquiv η (indicWord T) i = blockVec B₀ i
  rw [cliqueCoordEquiv_apply, blockVec_apply]
  by_cases hi : (i : Fin 24) ∈ B₀
  · have hm : η.symm i ∈ (indicWord T).support := by
      rw [support_indicWord, hT, Finset.mem_filter, Equiv.apply_symm_apply]
      exact ⟨Finset.mem_univ _, hi⟩
    simp only [hi, ↓reduceIte]
    exact zmod_two_eq_one _ (Finsupp.mem_support_iff.1 hm)
  · have hm : η.symm i ∉ (indicWord T).support := by
      rw [support_indicWord, hT, Finset.mem_filter, Equiv.apply_symm_apply]
      exact fun h => hi h.2
    simp only [hi, ↓reduceIte]
    exact Finsupp.notMem_support_iff.1 hm

include hC in
theorem map_cliqueCode_eq_K₀
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z)) :
    (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀ := by
  obtain ⟨_, -, -, h12, -⟩ := hS.clique_code_steiner_design hC
  refine eq_K₀ (E₀_le_map_cliqueCode η hη) (by rw [LinearEquiv.finrank_map_eq, h12]) fun g => ?_
  obtain ⟨x, rfl⟩ := θ.surjective g
  obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective x
  rintro _ ⟨w, hw, rfl⟩
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, rho₀_apply,
    ← cliqueCoordEquiv_mapDomain η (σ := setStabPerm act lab Y C f)
    (τ := psiX (θ f)) (fun z => Subtype.ext (hθ f z)) w]
  exact ⟨_, mapDomain_mem_cliqueCode hS.lab_act (fun x hx => (f.2.2 x).2 hx) _ (fun _ => rfl) hw,
    rfl⟩

end Code

end IsFischerSlice

section Module

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Finite C]
  {η : C ≃ X₀}

theorem ker_cliqueCoordQuot (hK : (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀) :
    LinearMap.ker (cliqueCoordQuot η) = LinearMap.ker (cliqueLabelMap lab C) := by
  ext w
  rw [LinearMap.mem_ker, cliqueCoordQuot_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← hK, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rfl

variable (lab) in
@[expose] def cliqueModuleEquiv
    (hK : (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀) :
    Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀ :=
  ((cliqueLabelMap lab C).quotKerEquivOfSurjective cliqueLabelMap_surjective).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (ker_cliqueCoordQuot hK).symm ≪≫ₗ
      (cliqueCoordQuot η).quotKerEquivOfSurjective (cliqueCoordQuot_surjective η))

theorem cliqueModuleEquiv_cliqueLabelMap
    (hK : (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀) (w : C →₀ ZMod 2) :
    cliqueModuleEquiv lab hK (cliqueLabelMap lab C w) = cliqueCoordQuot η w := by
  have h : ((cliqueLabelMap lab C).quotKerEquivOfSurjective cliqueLabelMap_surjective).symm
      (cliqueLabelMap lab C w) = Submodule.Quotient.mk w := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [cliqueModuleEquiv, LinearEquiv.trans_apply, h, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem cliqueModuleEquiv_gen (hK : (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀)
    (z : C) : cliqueModuleEquiv lab hK (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)) := by
  rw [← one_smul (ZMod 2) (Additive.ofMul (cliqueGen z)), ← cliqueLabelMap_single,
    cliqueModuleEquiv_cliqueLabelMap, cliqueCoordQuot_apply, cliqueCoordEquiv_single]

theorem comp_cliqueLabelMap_eq {ψ : Additive (Subgroup.closure (lab '' C)) →ₗ[ZMod 2] W₀}
    (hψ : ∀ z : C, ψ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) (w : C →₀ ZMod 2) :
    ψ (cliqueLabelMap lab C w) = cliqueCoordQuot η w := by
  have h : ψ ∘ₗ cliqueLabelMap lab C = cliqueCoordQuot η := Finsupp.lhom_ext fun z b => by
    rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul, map_smul,
      cliqueLabelMap_single, one_smul, hψ, cliqueCoordQuot_apply, cliqueCoordEquiv_single]
  exact LinearMap.congr_fun h w

theorem eq_cliqueModuleEquiv (hK : (cliqueCode lab C).map (cliqueCoordEquiv η).toLinearMap = K₀)
    {ψ : Additive (Subgroup.closure (lab '' C)) →ₗ[ZMod 2] W₀}
    (hψ : ∀ z : C, ψ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) :
    ψ = (cliqueModuleEquiv lab hK).toLinearMap := LinearMap.ext fun x => by
  obtain ⟨w, rfl⟩ := cliqueLabelMap_surjective (lab := lab) x
  rw [comp_cliqueLabelMap_eq hψ, LinearEquiv.coe_coe, cliqueModuleEquiv_cliqueLabelMap]

end Module

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem map_conj_eq_rhoW
    {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    [Finite C] {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {ψ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hψ : ∀ z : C, ψ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
    (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)) :
    ψ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (ψ (Additive.ofMul r)) := by
  obtain ⟨w, hw⟩ := cliqueLabelMap_surjective (lab := lab) (Additive.ofMul r)
  have hconj : cliqueLabelMap lab C (Finsupp.mapDomain (setStabPerm act lab Y C f) w) =
      Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩ := by
    rw [cliqueLabelMap_mapDomain hS.lab_act (fun x hx => (f.2.2 x).2 hx) _ (fun _ => rfl), hw]
    rfl
  have hc : ∀ w, ψ (cliqueLabelMap lab C w) = cliqueCoordQuot η w :=
    comp_cliqueLabelMap_eq (ψ := ψ.toLinearMap) hψ
  rw [← hconj, ← hw, hc, hc, cliqueCoordQuot_apply,
    cliqueCoordQuot_apply,
    cliqueCoordEquiv_mapDomain η (τ := psiX (θ f)) (fun z => Subtype.ext (hθ f z)),
    ← rho₀_apply, ← rhoW_mkQ]

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
