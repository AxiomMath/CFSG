module

public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type*} [Group G]

@[expose] def scriptY4 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY A ∧ Y = oPrimeResidualOf 3 Y ∧ Y = delta A LB Y ∧
    CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)}

@[expose] def scriptY0 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY4 A LB ∧ Y ∈ scriptY2 A}

@[expose] def scriptY0Star (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | Maximal (· ∈ scriptY0 A LB) Y}

theorem mem_scriptY4_iff {A Y : Subgroup G} {LB : Subgroup G → Subgroup G} :
    Y ∈ scriptY4 A LB ↔ Y ∈ scriptY A ∧ Y = oPrimeResidualOf 3 Y ∧ Y = delta A LB Y ∧
      CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  Iff.rfl

theorem scriptY0Star_subset (A : Subgroup G) (LB : Subgroup G → Subgroup G) :
    scriptY0Star A LB ⊆ scriptY0 A LB :=
  fun _ hY => hY.prop

end CFSG.RankThree.PartTwo.Sec15
