module

public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type*} [Group G]

@[expose] def scriptY3Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | Maximal (· ∈ scriptY3 A LB) Y}

@[expose] def scriptY1 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY3 A LB ∧ oPrimeResidualOf 3 Y = ⊥}

@[expose] def scriptY1Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | Maximal (· ∈ scriptY1 A LB) Y}

@[expose] def scriptYs (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY1 A LB ∧ Group.IsSolvable Y}

@[expose] def charNormalizerJoin (T X : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≤ T) (_ : (C.subgroupOf T).Characteristic) (_ : C ≠ ⊥),
    X ⊓ Subgroup.normalizer (C : Set G)

theorem inf_normalizer_le_charNormalizerJoin {T X C : Subgroup G} (hCT : C ≤ T)
    (hC : (C.subgroupOf T).Characteristic) (hC1 : C ≠ ⊥) :
    X ⊓ Subgroup.normalizer (C : Set G) ≤ charNormalizerJoin T X :=
  le_iSup_of_le C (le_iSup_of_le hCT (le_iSup_of_le hC (le_iSup_of_le hC1 le_rfl)))

theorem charNormalizerJoin_le (T X : Subgroup G) : charNormalizerJoin T X ≤ X :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left

theorem scriptY1Star_subset (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    scriptY1Star A LB ⊆ scriptY1 A LB :=
  fun _ hY => hY.prop

theorem scriptY3Star_subset (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    scriptY3Star A LB ⊆ scriptY3 A LB :=
  fun _ hY => hY.prop

end CFSG.RankThree.PartTwo.Sec16
