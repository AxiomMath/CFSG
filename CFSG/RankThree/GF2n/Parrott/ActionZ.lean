module

public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.RankThree.GF2n.Parrott.Setup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem centerIn_le_H (z : G) : centerIn (J z) ≤ H z :=
  (le_of_eq (centerIn_eq_map_center (J z))).trans
    ((Subgroup.map_subtype_le (Subgroup.center (J z))).trans (J_le_H (z := z)))

theorem centerIn_subgroupOf_eq_inf_centralizer (z : G) :
    (centerIn (J z)).subgroupOf (H z) =
      ((J z).subgroupOf (H z)) ⊓
        Subgroup.centralizer (((J z).subgroupOf (H z)) : Set (H z)) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨hx.1, ?_⟩
    change ∀ y ∈ ((J z).subgroupOf (H z) : Set (H z)), y * x = x * y
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : G) hy)
  · rintro ⟨hxJ, hxC⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨hxJ, ?_⟩
    change ∀ y ∈ (J z : Set G), y * (x : G) = (x : G) * y
    intro y hy
    have hyH : y ∈ H z := J_le_H (z := z) hy
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hxC ⟨y, hyH⟩ hy)

theorem centerIn_subgroupOf_eq_center_map (z : G) :
    (centerIn (J z)).subgroupOf (H z) =
      (Subgroup.center ((J z).subgroupOf (H z))).map
        ((J z).subgroupOf (H z)).subtype := by
  rw [center_map_subtype_eq_inf_centralizer]
  exact centerIn_subgroupOf_eq_inf_centralizer z

instance centerIn_subgroupOf_normal (z : G) :
    ((centerIn (J z)).subgroupOf (H z)).Normal := by
  rw [centerIn_subgroupOf_eq_center_map]
  infer_instance

@[expose] noncomputable def conjZ (z : G) : H z →* MulAut (centerIn (J z)) :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe (centerIn_le_H (z := z)))).toMonoidHom.comp
    (MulAut.conjNormal (H := (centerIn (J z)).subgroupOf (H z)))

theorem conjZ_apply_coe (g : H z) (x : centerIn (J z)) :
    ((conjZ z g x : centerIn (J z)) : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
  simp [conjZ, MulAut.congr, MulEquiv.trans_apply, MulAut.conjNormal_apply,
    Subgroup.subgroupOfEquivOfLe]

theorem J_le_ker_conjZ (z : G) :
    (J z).subgroupOf (H z) ≤ (conjZ z).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change ((conjZ z g x : centerIn (J z)) : G) = (x : G)
  rw [conjZ_apply_coe]
  have hgJ : (g : G) ∈ J z := Subgroup.mem_subgroupOf.mp hg
  have hcomm : (g : G) * (x : G) = (x : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp x.2.2 (g : G) hgJ
  rw [hcomm, mul_inv_cancel_right]

@[expose] noncomputable def actionZ (z : G) :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) →* MulAut (centerIn (J z)) :=
  QuotientGroup.lift _ (conjZ z) (J_le_ker_conjZ z)

@[simp] theorem actionZ_mk (z : G) (g : H z) :
    actionZ z (QuotientGroup.mk' ((J z).subgroupOf (H z)) g) = conjZ z g :=
  QuotientGroup.lift_mk' _ _ g

@[expose] noncomputable def actionZQA45
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientData (z := z) hN) :
    QA45.originalSubgroup →* MulAut (centerIn (J z)) :=
  (actionZ z).comp D.toQA45.symm.toMonoidHom

theorem actionZQA45_apply
    {hN : ((J z).subgroupOf (H z)).Normal} (D : QuotientData (z := z) hN)
    (a : QA45.originalSubgroup) :
    actionZQA45 (z := z) D a = actionZ z (D.toQA45.symm a) := rfl

end CFSG.RankThree.GF2n.Parrott
