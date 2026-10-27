module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] def Dz : Subgroup G := t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G)

@[expose] noncomputable def Xz : Subgroup G :=
  (Subgroup.normalClosure ((t.Z.subgroupOf (Subgroup.centralizer ({t.y} : Set G)) :
    Subgroup ↥(Subgroup.centralizer ({t.y} : Set G))) :
      Set ↥(Subgroup.centralizer ({t.y} : Set G)))).map
    (Subgroup.centralizer ({t.y} : Set G)).subtype

@[expose] noncomputable def Oz : Subgroup G := (CFSG.pPrimeCore 3 ↥t.Xz).map t.Xz.subtype

theorem Dz_le_Ky : t.Dz ≤ t.Ky := t.inf_centralizer_le_Ky

theorem Xz_le_centralizer : t.Xz ≤ Subgroup.centralizer ({t.y} : Set G) :=
  Subgroup.map_subtype_le _

theorem Z_le_Xz : t.Z ≤ t.Xz := by
  intro x hx
  refine ⟨⟨x, t.Z_le_centralizer hx⟩, Subgroup.subset_normalClosure ?_, rfl⟩
  exact hx

theorem normal_Xz :
    (t.Xz.subgroupOf (Subgroup.centralizer ({t.y} : Set G))).Normal := by
  rw [Xz, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  exact Subgroup.normalClosure_normal

theorem Oz_le_Xz : t.Oz ≤ t.Xz := Subgroup.map_subtype_le _

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
