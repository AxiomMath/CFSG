module
public import Mathlib.Algebra.Group.Subgroup.Ker
open Subgroup

public noncomputable section
namespace Subgroup
theorem exists_mulEquiv_map_range_of_leftInverse {G S : Type*} [Group G] [Group S]
    (H : Subgroup G) (σ : S →* H) (π : H →* S)
    (hσ : Function.LeftInverse π σ) :
    let J : Subgroup G := σ.range.map H.subtype
    ∃ η : ↥J ≃* S, ∀ j : ↥J, ∀ hj : (j : G) ∈ H, η j = π ⟨(j : G), hj⟩ := by
  let J : Subgroup G := σ.range.map H.subtype
  have hσinj : Function.Injective σ := Function.LeftInverse.injective hσ
  let eσ : S ≃* σ.range := MonoidHom.ofInjective hσinj
  let eMap : σ.range ≃* J := Subgroup.equivMapOfInjective σ.range H.subtype H.subtype_injective
  let η : J ≃* S := eMap.symm.trans eσ.symm
  refine ⟨η, ?_⟩
  intro j hj
  change eσ.symm (eMap.symm j) = π ⟨(j : G), hj⟩
  have hc : (((eMap.symm j : σ.range) : H) : G) = (j : G) := by
    calc
      _ = ((eMap (eMap.symm j) : J) : G) := by
        symm
        exact Subgroup.coe_equivMapOfInjective_apply σ.range H.subtype
          H.subtype_injective (eMap.symm j)
      _ = (j : G) := congrArg Subtype.val (eMap.apply_symm_apply j)
  have hh : ((eMap.symm j : σ.range) : H) = (⟨(j : G), hj⟩ : H) := Subtype.ext hc
  rw [← hh]
  apply eσ.injective
  rw [eσ.apply_symm_apply]
  apply Subtype.ext
  change ((eMap.symm j : σ.range) : H) = σ (π ((eMap.symm j : σ.range) : H))
  obtain ⟨s, hs⟩ := (eMap.symm j).2
  rw [← hs, hσ]
end Subgroup
