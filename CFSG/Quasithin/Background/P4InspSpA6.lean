module

public import CFSG.Quasithin.Background.P4InspSpEmbed
public import CFSG.Quasithin.Background.G9StmtsModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix

namespace G11

namespace P4InspSp

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem p4inspsp_a6_case [Finite U] {f : LinearMap.BilinForm (ZMod 2) U} (h : IsSymplectic f)
    (hd : Module.finrank (ZMod 2) U = 4) {M K : Subgroup (GLV U)}
    (hPM : ⁅spSub f, spSub f⁆ ≤ M) (hMle : M ≤ spSub f) (hKM : K ≤ M)
    (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hirr : IsIrr K ⊤)
    (hperf : Group.IsPerfect ↥K) :
    IsSimpleGroup ↥K ∧ IsPermCoreModule K (alternatingGroup (Fin 6)) := by
  obtain ⟨Mo⟩ := p4inspsp_exists_model h hd
  obtain ⟨ρ, hinj, hmem, hβ, hrange⟩ := p4inspsp_exists_embedding h hd Mo
  have hrange' : ρ.range = spSub f := le_antisymm (by rintro _ ⟨σ, rfl⟩; exact hmem σ) hrange
  have hPcomm : ⁅spSub f, spSub f⁆ = Subgroup.map ρ (alternatingGroup (Fin 6)) := by
    rw [← hrange']
    exact p4inspsp_commutator_range (by norm_num) ρ
  have hKP : K ≤ Subgroup.map ρ (alternatingGroup (Fin 6)) :=
    p4inspsp_perfect_le_map_alt (by norm_num) ρ (hrange' ▸ hKM.trans hMle)
      (Subgroup.isPerfect_iff.1 hperf)
  have hPM : Subgroup.map ρ (alternatingGroup (Fin 6)) ≤ M := hPcomm ▸ hPM
  have : IsSimpleGroup ↥(Subgroup.map ρ (alternatingGroup (Fin 6))) :=
    p4inspsp_isSimpleGroup_map_alt (by norm_num) ρ hinj
  have hKeq : K = Subgroup.map ρ (alternatingGroup (Fin 6)) :=
    p4inspsp_eq_of_normalized hKP (fun p hp k hk => hnorm p (hPM hp) k hk)
      (p4inspsp_ne_bot hirr (by omega))
  refine ⟨by rw [hKeq]; exact inferInstance, ?_⟩
  let e : ↥K ≃* ↥(alternatingGroup (Fin 6)) :=
    (MulEquiv.subgroupCongr hKeq).trans (Subgroup.equivMapOfInjective _ ρ hinj).symm
  have he : ∀ γ : ↥K,
      (γ : GLV U) = ρ ((e γ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) := by
    intro γ
    have h1 := Subgroup.coe_equivMapOfInjective_apply (alternatingGroup (Fin 6)) ρ hinj (e γ)
    have h2 : (Subgroup.equivMapOfInjective (alternatingGroup (Fin 6)) ρ hinj) (e γ) =
        MulEquiv.subgroupCongr hKeq γ := MulEquiv.apply_symm_apply _ _
    rw [h2] at h1
    exact h1
  refine ⟨e, Mo.β, Mo.surj, fun u => ?_, fun γ u u' hu' => ?_⟩
  · rw [Mo.ker u]
    constructor
    · rintro (h0 | h1)
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr ⟨by decide, h1⟩
    · rintro (h0 | ⟨-, h1⟩)
      · exact Or.inl (congrArg Subtype.val h0)
      · exact Or.inr h1
  · rw [he γ, hβ]
    congr 1
    exact Subtype.ext hu'

end P4InspSp

end G11

end CFSG.Quasithin
