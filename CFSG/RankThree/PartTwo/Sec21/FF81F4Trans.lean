
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.LangFiniteSubfieldCongruence
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Transport

variable {X : Type} [Group X] {Y : Subgroup X} {C : Type} [Group C] (e : ↥Y ≃* C)

@[expose] def ιY : C →* X := Y.subtype.comp e.symm.toMonoidHom

theorem ιY_apply (c : C) : ιY e c = (e.symm c : X) := rfl

theorem ιY_injective : Function.Injective (ιY e) := fun a b h =>
  e.symm.injective (Subtype.ext h)

theorem ιY_mem (c : C) : ιY e c ∈ Y := (e.symm c).2

theorem ιY_e (y : ↥Y) : ιY e (e y) = (y : X) := by
  rw [ιY_apply, MulEquiv.symm_apply_apply]

theorem range_ιY : (ιY e).range = Y := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ιY_mem e c
  · intro hx
    exact ⟨e ⟨x, hx⟩, ιY_e e ⟨x, hx⟩⟩

theorem map_cen_ιY (c : C) : (Cen c).map (ιY e) = Y ⊓ Cen (ιY e c) := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨ιY_mem e d, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 hd
    rw [← map_mul, ← map_mul, this]
  · rintro ⟨hzY, hz⟩
    refine ⟨e ⟨z, hzY⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, ιY_e e ⟨z, hzY⟩⟩
    apply ιY_injective e
    rw [map_mul, map_mul, ιY_e]
    exact Subgroup.mem_centralizer_singleton_iff.1 hz

theorem card_inf_cen {x : X} (hx : x ∈ Y) :
    Nat.card ↥(Y ⊓ Cen x) = Nat.card ↥(Cen (e ⟨x, hx⟩)) := by
  have h := map_cen_ιY e (e ⟨x, hx⟩)
  rw [ιY_e] at h
  rw [← h]
  exact Subgroup.card_map_of_injective (ιY_injective e)

@[expose] def toC (U : Subgroup X) : Subgroup C := U.comap (ιY e)

theorem mem_toC {U : Subgroup X} {c : C} : c ∈ toC e U ↔ ιY e c ∈ U := Iff.rfl

theorem map_toC {U : Subgroup X} (hU : U ≤ Y) : (toC e U).map (ιY e) = U := by
  rw [toC, Subgroup.map_comap_eq, range_ιY]
  exact inf_of_le_right hU

theorem card_toC {U : Subgroup X} (hU : U ≤ Y) : Nat.card ↥(toC e U) = Nat.card ↥U := by
  conv_rhs => rw [← map_toC e hU]
  exact (Subgroup.card_map_of_injective (ιY_injective e)).symm

theorem toC_le {U V : Subgroup X} (h : U ≤ V) : toC e U ≤ toC e V := Subgroup.comap_mono h

theorem toC_injective {U V : Subgroup X} (hU : U ≤ Y) (hV : V ≤ Y) (h : toC e U = toC e V) :
    U = V := by
  rw [← map_toC e hU, ← map_toC e hV, h]

theorem mem_conjBy_iff {G : Type} [Group G] {g x : G} {H : Subgroup G} :
    x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem toC_conjBy (U : Subgroup X) (c : C) :
    toC e (conjBy (ιY e c) U) = conjBy c (toC e U) := by
  ext d
  rw [mem_toC, mem_conjBy_iff, mem_conjBy_iff, mem_toC, map_mul, map_mul, map_inv]

theorem exists_conj_iff {x z : X} (hx : x ∈ Y) (hz : z ∈ Y) :
    (∃ y ∈ Y, y * x * y⁻¹ = z) ↔ ∃ c : C, c * e ⟨x, hx⟩ * c⁻¹ = e ⟨z, hz⟩ := by
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨e ⟨y, hy⟩, ?_⟩
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext h
  · rintro ⟨c, h⟩
    refine ⟨ιY e c, ιY_mem e c, ?_⟩
    have := congrArg (ιY e) h
    rw [map_mul, map_mul, map_inv, ιY_e, ιY_e] at this
    exact this

end Transport

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
