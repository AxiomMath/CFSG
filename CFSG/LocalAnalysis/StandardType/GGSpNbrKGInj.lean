module

public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGQuot

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem exists_inj_hom_centerQuot {G A : Type*} {R : Type} [Group G] [Group A] [Group R]
    {K' J : Subgroup G} (θ : K' ⧸ Subgroup.center K' ≃* R) (ψ : A →* G)
    (hψ : Function.Injective ψ) (hψJ : ψ.range = J) (hJK : J ≤ K')
    (hZ : Subgroup.center J = ⊥) :
    ∃ ψ' : A →* R, Function.Injective ψ' ∧
      ψ'.range = (J.subgroupOf K').map (ggCenterQuotHom θ) := by
  let psi0 : A →* K' := ψ.codRestrict K' fun a => hJK (hψJ ▸ ⟨a, rfl⟩)
  have hrange : psi0.range = J.subgroupOf K' := by
    ext k
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact hψJ ▸ ⟨a, rfl⟩
    · intro hk
      have hk' : (k : G) ∈ ψ.range := hψJ.symm ▸ hk
      rcases hk' with ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
  refine ⟨(ggCenterQuotHom θ).comp psi0, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    rw [MonoidHom.comp_apply] at ha
    have hmemK : psi0 a ∈ Subgroup.center K' := by
      rw [← ggCenterQuotHom_ker θ, MonoidHom.mem_ker]
      exact ha
    have hmemJ : (⟨ψ a, hψJ ▸ ⟨a, rfl⟩⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      have hj := Subgroup.mem_center_iff.mp hmemK (Subgroup.inclusion hJK j)
      exact congrArg (fun x : K' => (x : G)) hj
    have hz1 : (⟨ψ a, hψJ ▸ ⟨a, rfl⟩⟩ : J) = 1 :=
      Subgroup.mem_bot.mp (hZ ▸ hmemJ)
    have hψa1 : ψ a = 1 := by
      simpa using congrArg Subtype.val hz1
    exact hψ (by rw [hψa1, map_one])
  · rw [MonoidHom.range_comp, hrange]

end CFSG.StandardType
