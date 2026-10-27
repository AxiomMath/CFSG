module

public import CFSG.Quasithin.Vol2.Ch3E213MP5C
public import CFSG.Quasithin.Vol2.Ch3E213MP5E
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Subgroup CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {A : Type*} [Group A] {K : Subgroup A} {k : Type} [Field k]

@[expose] noncomputable def cornerA (θ : ↥K ≃* projectiveSL 3 k) : SL(2, k) →* A :=
  K.subtype.comp (θ.symm.toMonoidHom.comp (cornerHom k))

theorem cornerA_injective (θ : ↥K ≃* projectiveSL 3 k) : Function.Injective (cornerA θ) :=
  K.subtype_injective.comp (θ.symm.injective.comp cornerHom_injective)

theorem map_cornerA (θ : ↥K ≃* projectiveSL 3 k) (X : Subgroup SL(2, k)) :
    X.map (cornerA θ) = ((X.map (cornerHom k)).map θ.symm.toMonoidHom).map K.subtype := by
  rw [cornerA, ← Subgroup.map_map, ← Subgroup.map_map]

theorem range_cornerA_le (θ : ↥K ≃* projectiveSL 3 k) : (cornerA θ).range ≤ K := by
  rintro _ ⟨g, rfl⟩
  exact (θ.symm (cornerHom k g)).2

theorem inf_map_eq (θ : ↥K ≃* projectiveSL 3 k) {X : Subgroup A}
    {Z Y : Subgroup (projectiveSL 3 k)} (hX : ((X ⊓ K).subgroupOf K).map θ.toMonoidHom = Z) :
    X ⊓ (Y.map θ.symm.toMonoidHom).map K.subtype =
      ((Z ⊓ Y).map θ.symm.toMonoidHom).map K.subtype := by
  have hXK : X ⊓ K = (Z.map θ.symm.toMonoidHom).map K.subtype := by
    rw [← hX, map_symm_map, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  rw [Subgroup.map_inf _ _ _ θ.symm.injective, Subgroup.map_inf _ _ _ K.subtype_injective, ← hXK,
    inf_assoc, inf_eq_right.2 (Subgroup.map_subtype_le _)]

theorem inf_range_cornerA_S (θ : ↥K ≃* projectiveSL 3 k) {S : Subgroup A}
    (hθS : ((S ⊓ K).subgroupOf K).map θ.toMonoidHom = projUnitriangular 3 k) :
    S ⊓ (cornerA θ).range = (sl2UpperUnipotentSubgroup k).map (cornerA θ) := by
  rw [MonoidHom.range_eq_map, map_cornerA, map_cornerA, ← MonoidHom.range_eq_map,
    inf_map_eq θ hθS, projUnitriangular_inf_range, map_sl2UpperUnipotent]

theorem inf_range_cornerA_B (θ : ↥K ≃* projectiveSL 3 k) {B : Subgroup A}
    (hθB : ((B ⊓ K).subgroupOf K).map θ.toMonoidHom = projUpperTriangular 3 k) :
    B ⊓ (cornerA θ).range = (sl2Borel k).map (cornerA θ) := by
  rw [MonoidHom.range_eq_map, map_cornerA, map_cornerA, ← MonoidHom.range_eq_map,
    inf_map_eq θ hθB, projUpperTriangular_inf_range]

end CFSG.Quasithin.Ch3E213M.P5
