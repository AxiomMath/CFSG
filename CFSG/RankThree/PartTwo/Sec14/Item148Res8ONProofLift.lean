module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148

variable {G : Type} [Group G] [Finite G]

namespace Res8ON

theorem isQuasisimple_of_isTripleCover {X Y : Type*} [Group X] [Group Y] [IsSimpleGroup Y]
    (hXp : Group.IsPerfect X) (htc : Sec4.IsTripleCover X Y) : IsQuasisimple X := by
  obtain ⟨-, ⟨φ⟩⟩ := htc
  have hs : IsSimpleGroup (X ⧸ Subgroup.center X) := MulEquiv.isSimpleGroup φ
  have : Nontrivial (X ⧸ Subgroup.center X) := hs.toNontrivial
  have : Group.IsPerfect X := hXp
  have hp : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  exact ⟨hXp, hs, exists_ne_comm_of_isPerfect hp⟩

end Res8ON

end CFSG.RankThree.PartTwo.Sec14
