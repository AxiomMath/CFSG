module

public import CFSG.Quasithin.AppendixH.Common.InducedAut
public import CFSG.Quasithin.AppendixH.Common.OctadAltHom
public import CFSG.Quasithin.AppendixH.H16.OctadQuad
public import CFSG.Quasithin.AppendixH.H16.OmegaPlus6

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] noncomputable def octRho : ↥(octStab octad0) →* MulAut W11 :=
  (rhoC11 AutPerm le_rfl).comp (Subgroup.inclusion octStab_octad0_le_AutPerm)

theorem octRho_apply (γ : ↥(octStab octad0)) (x : W11) :
    octRho γ x = rhoC11 AutPerm le_rfl ⟨(γ : S24), octStab_octad0_le_AutPerm γ.2⟩ x := rfl

theorem octBeta_octRho_eq_one_iff (γ : ↥(octStab octad0)) (x : W11) :
    octBeta (octRho γ x) = 1 ↔ octBeta x = 1 := by
  refine Iff.trans (octBeta_eq_one_iff (octRho γ x)) ?_
  refine Iff.trans ?_ (octBeta_eq_one_iff x).symm
  have hmem : octRho γ ∈ imgCd (octStab octad0) :=
    rhoCd_mem_imgCd (octStab_octad0_le_AutPerm γ.2) γ.2
  have hmem' : octRho γ⁻¹ ∈ imgCd (octStab octad0) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hmem
  constructor
  · intro hx
    have h := isActsInv_octV5 (octRho γ⁻¹) ⟨octRho γ⁻¹, hmem', rfl⟩ (octRho γ x) hx
    have hx' : octRho γ⁻¹ (octRho γ x) = x := by
      rw [map_inv, MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply (octRho γ) x
    rwa [hx'] at h
  · intro hx
    exact isActsInv_octV5 (octRho γ) ⟨octRho γ, hmem, rfl⟩ x hx

theorem exists_octPhi : ∃ Φ : ↥(octStab octad0) →* MulAut (Wn 6),
    ∀ (γ : ↥(octStab octad0)) (x : W11), Φ γ (octBeta x) = octBeta (octRho γ x) :=
  exists_hom_induced octBeta octBeta_surjective octRho octBeta_octRho_eq_one_iff

@[expose] noncomputable def octPhi : ↥(octStab octad0) →* MulAut (Wn 6) :=
  Classical.choose exists_octPhi

theorem octPhi_apply (γ : ↥(octStab octad0)) (x : W11) :
    octPhi γ (octBeta x) = octBeta (octRho γ x) :=
  Classical.choose_spec exists_octPhi γ x

theorem ker_octPhi :
    octPhi.ker = (fixO).subgroupOf (octStab octad0) := by
  have hback : ∀ k : ↥(octStab octad0), (k : S24) ∈ fixO → octPhi k = 1 := by
    intro k hk
    obtain ⟨t, ht⟩ := (mem_fixO_iff (k : S24)).1 hk
    refine MulEquiv.ext fun w => ?_
    obtain ⟨x, rfl⟩ := octBeta_surjective w
    rw [octPhi_apply]
    have hko : octRho k = ko11 t := by
      have hsub : Subgroup.inclusion octStab_octad0_le_AutPerm k =
          (⟨koPerm t, (koPerm_mem_mog22 t).1.1⟩ : ↥AutPerm) := Subtype.ext ht
      exact congrArg (fun g : ↥AutPerm => rhoC11 AutPerm le_rfl g) hsub
    have hfix : octBeta (ko11 t x) = octBeta x := by
      have h := (octBeta_eq_one_iff (ko11 t x * x⁻¹)).2 (ko11_mul_inv_mem t x)
      rw [map_mul, map_inv] at h
      exact mul_inv_eq_one.mp h
    rw [hko, hfix]
    rfl
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hγ
    let N : Subgroup S24 := octPhi.ker.map (octStab octad0).subtype
    have h1 : octFix octad0 ≤ N := by
      intro σ hσ
      refine ⟨⟨σ, octFix_le_octStab octad0 hσ⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr
        (hback ⟨σ, octFix_le_octStab octad0 hσ⟩ (by simpa [octFix_octad0] using hσ))
    have h2 : N ≤ octStab octad0 := by
      rintro σ ⟨k, -, rfl⟩
      exact k.2
    have h3 : (N.subgroupOf (octStab octad0)).Normal := by
      have heq : N.subgroupOf (octStab octad0) = octPhi.ker :=
        Subgroup.comap_map_eq_self_of_injective (octStab octad0).subtype_injective octPhi.ker
      rw [heq]
      exact MonoidHom.normal_ker octPhi
    have hG1not : octG1 ∉ N := by
      intro hmem
      obtain ⟨k, hk, hkσ⟩ := Subgroup.mem_map.mp hmem
      have hk' : k = (⟨octG1, octG1_mem_octStab⟩ : ↥(octStab octad0)) := Subtype.ext hkσ
      have hk1 : octPhi (⟨octG1, octG1_mem_octStab⟩ : ↥(octStab octad0)) = 1 := by
        rw [← hk']
        exact MonoidHom.mem_ker.mp hk
      obtain ⟨m, -, hmne⟩ := octG1_acts_nontrivially_masks
      have hEq : octPhi (⟨octG1, octG1_mem_octStab⟩ : ↥(octStab octad0))
          (octBeta (toW 11 m)) = octBeta (toW 11 m) := by
        simpa using congrArg (fun f : MulAut (Wn 6) => f (octBeta (toW 11 m))) hk1
      rw [octPhi_apply, octRho_apply,
        rhoC11_toW AutPerm le_rfl
          (⟨octG1, octStab_octad0_le_AutPerm octG1_mem_octStab⟩ : ↥AutPerm) hasArr_octG1 m,
        octBeta_toW, octBeta_toW] at hEq
      exact hmne (toW_inj (actM_lt octBetaCols_lt _) (actM_lt octBetaCols_lt _) hEq)
    rcases eq_octFix_or_eq_octStab_of_normal isOctad_octad0 h1 h2 h3 with hN | hN
    · have hmem : (γ : S24) ∈ N :=
        Subgroup.mem_map.mpr ⟨γ, MonoidHom.mem_ker.mpr hγ, rfl⟩
      rw [hN] at hmem
      rwa [octFix_octad0] at hmem
    · rw [hN] at hG1not
      exact absurd octG1_mem_octStab hG1not
  · intro hγ
    exact hback γ hγ

theorem mulInv_mem_octV5_iff (γ : ↥AutPerm)
    (hγ : (γ : S24) ∈ octStab octad0) :
    (∀ x : W11, rhoC11 AutPerm le_rfl γ x * x⁻¹ ∈ octV5) ↔ (γ : S24) ∈ fixO := by
  let γ' : ↥(octStab octad0) := ⟨(γ : S24), hγ⟩
  have hρ : octRho γ' = rhoC11 AutPerm le_rfl γ := by
    have hsub : Subgroup.inclusion octStab_octad0_le_AutPerm γ' = γ := Subtype.ext rfl
    exact congrArg (fun g : ↥AutPerm => rhoC11 AutPerm le_rfl g) hsub
  have h1 : (∀ x : W11, rhoC11 AutPerm le_rfl γ x * x⁻¹ ∈ octV5) ↔
      ∀ x : W11, octBeta (rhoC11 AutPerm le_rfl γ x) = octBeta x := by
    constructor
    · intro h x
      have hx := (octBeta_eq_one_iff (rhoC11 AutPerm le_rfl γ x * x⁻¹)).2 (h x)
      rw [map_mul, map_inv] at hx
      exact mul_inv_eq_one.mp hx
    · intro h x
      exact (octBeta_eq_one_iff _).1 (by
        rw [map_mul, map_inv, h x]
        exact mul_inv_cancel _)
  have h2 : (∀ x : W11, octBeta (rhoC11 AutPerm le_rfl γ x) = octBeta x) ↔ octPhi γ' = 1 := by
    constructor
    · intro h
      refine MulEquiv.ext fun w => ?_
      obtain ⟨x, rfl⟩ := octBeta_surjective w
      rw [octPhi_apply, hρ, h x]
      rfl
    · intro h x
      have hx := congrArg (fun f : MulAut (Wn 6) => f (octBeta x)) h
      rw [octPhi_apply, hρ] at hx
      simpa using hx
  exact Iff.trans h1 (Iff.trans h2 (by
    rw [← MonoidHom.mem_ker, ker_octPhi]
    exact Subgroup.mem_subgroupOf))

theorem octPhi_isometry (γ : ↥(octStab octad0)) (x : Fin 6 → ZMod 2) :
    qPlus6 (Multiplicative.toAdd (octPhi γ (Multiplicative.ofAdd x))) = qPlus6 x := by
  obtain ⟨y, hy⟩ := octBeta_surjective (Multiplicative.ofAdd x)
  rw [← hy, octPhi_apply, octRho_apply]
  rw [qPlus6_octBeta_rhoC11
    (⟨(γ : S24), octStab_octad0_le_AutPerm γ.2⟩ : ↥AutPerm) γ.2 y]
  rw [hy, toAdd_ofAdd]

theorem card_range_octPhi : Nat.card octPhi.range = 20160 := by
  have hker : Nat.card octPhi.ker = 16 := by
    rw [ker_octPhi, ← octFix_octad0]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (octFix_le_octStab octad0)).toEquiv).trans
      (card_octFix isOctad_octad0)
  have h := Subgroup.card_ker_mul_card_range octPhi
  rw [hker, card_octStab isOctad_octad0] at h
  omega

theorem range_octPhi : octPhi.range = omegaN 6 qPlus6 := by
  refine eq_omegaN_qPlus6_of_card octPhi.range ?_ card_range_octPhi
  intro g hg x
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hg
  exact octPhi_isometry γ x

theorem inducesOnVia_octBeta :
    InducesOnVia (imgCd (octStab octad0)) ⊤ octV5 (Multiplicative (Fin 6 → ZMod 2))
      (omegaN 6 qPlus6) (octBeta.comp (⊤ : Subgroup W11).subtype) := by
  refine ⟨le_top, fun _ _ _ _ => trivial, fun g hg z hz => isActsInv_octV5 g ⟨g, hg, rfl⟩ z hz,
    ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨x, rfl⟩ := octBeta_surjective w
    exact ⟨⟨x, trivial⟩, rfl⟩
  · intro u
    exact octBeta_eq_one_iff (u : W11)
  · rintro g hg
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨octPhi ⟨σ, Subgroup.mem_subgroupOf.mp hσ⟩, ?_, ?_⟩
    · rw [← range_octPhi]
      exact MonoidHom.mem_range.mpr ⟨⟨σ, Subgroup.mem_subgroupOf.mp hσ⟩, rfl⟩
    · intro u u' hu'
      have hρσ : octRho (⟨σ, Subgroup.mem_subgroupOf.mp hσ⟩ : ↥(octStab octad0)) =
          rhoC11 AutPerm le_rfl σ := by
        have hsub : Subgroup.inclusion octStab_octad0_le_AutPerm
            (⟨σ, Subgroup.mem_subgroupOf.mp hσ⟩ : ↥(octStab octad0)) = σ := Subtype.ext rfl
        exact congrArg (fun g : ↥AutPerm => rhoC11 AutPerm le_rfl g) hsub
      change octBeta (u' : W11) =
        octPhi (⟨σ, Subgroup.mem_subgroupOf.mp hσ⟩ : ↥(octStab octad0)) (octBeta (u : W11))
      rw [hu', octPhi_apply, hρσ]
  · rintro γ hγ
    rw [← range_octPhi] at hγ
    obtain ⟨σ', rfl⟩ := MonoidHom.mem_range.mp hγ
    refine ⟨octRho σ', ?_, ?_⟩
    · change rhoCd (octStab_octad0_le_AutPerm σ'.2) ∈ imgCd (octStab octad0)
      exact rhoCd_mem_imgCd (octStab_octad0_le_AutPerm σ'.2) σ'.2
    · intro u u' hu'
      change octBeta (u' : W11) = octPhi σ' (octBeta (u : W11))
      rw [hu', octPhi_apply]

end CFSG.ASVolI.H16
