module

public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace A36A

variable {G : Type*} [Group G]

theorem subgroupOf_solvRad [Finite G] (L : Subgroup G) :
    (solvRad L).subgroupOf L = CFSG.solvableRadical ↥L := by
  refine le_antisymm ?_ ?_
  · have := solvRad_isSolvable L
    have hs : Group.IsSolvable ↥((solvRad L).subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).injective
    exact A3.le_solvableRadical inferInstance hs
  · set R : Subgroup ↥L := CFSG.solvableRadical ↥L
    have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
    have hRL : R.map L.subtype ≤ L := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    have hRR : (R.map L.subtype).subgroupOf L = R :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective R
    have hn : ((R.map L.subtype).subgroupOf L).Normal := by
      rw [hRR]
      infer_instance
    have hs : Group.IsSolvable ↥(R.map L.subtype) :=
      Group.isSolvable_of_surjective
        (f := (R.equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
        (R.equivMapOfInjective _ _).surjective
    calc R = (R.map L.subtype).subgroupOf L := hRR.symm
      _ ≤ (solvRad L).subgroupOf L := Subgroup.comap_mono (le_solvRad hRL hn hs)

theorem isPerfect_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) : Group.IsPerfect ↥L :=
  Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL)

theorem top_commutator_of_mem_cComp {L X : Subgroup G} (hL : L ∈ cComp X) :
    ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
  rw [← commutator_def]
  exact Group.isPerfect_def.mp (isPerfect_of_mem_cComp hL)

theorem simple_quotient_of_mem_cComp [Finite G] {L X : Subgroup G} (hL : L ∈ cComp X) :
    IsSimpleGroup (↥L ⧸ CFSG.solvableRadical ↥L) ∧
      ∃ a b : ↥L ⧸ CFSG.solvableRadical ↥L, a * b ≠ b * a := by
  obtain ⟨-, ⟨hs, a, b, hab⟩, -⟩ := cComp_structure hL
  let e : ↥L ⧸ (solvRad L).subgroupOf L ≃* ↥L ⧸ CFSG.solvableRadical ↥L :=
    QuotientGroup.quotientMulEquivOfEq (subgroupOf_solvRad L)
  have := hs
  refine ⟨e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

end A36A

end CFSG.Quasithin
