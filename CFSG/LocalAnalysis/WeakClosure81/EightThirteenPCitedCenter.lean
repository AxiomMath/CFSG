module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
import CFSG.Adapters.LieModelSimple
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsU3 IsSp4)

private theorem wccq_lieModel_centerQuotient {X : Type} [Group X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hq : CFSG.Open.IsQuasisimple X)
    (ht : t ∈ CFSG.Blueprint.classicalTags) (h : CFSG.Blueprint.LieModel X t n p f) :
    CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t n p f := by
  haveI : IsSimpleGroup X := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  exact CFSG.Blueprint.LieModel.quotient_center
    (CFSG.ProperTwoGeneratedCore.RankOnePair.center_eq_bot_of_simple_perfect X) h

theorem isU3_centerQuotient_of_shapeU3 {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : ShapeU3 L) : IsU3 (↥L ⧸ Subgroup.center ↥L) 2 :=
  wccq_lieModel_centerQuotient (t := .PSU) (n := 3) (p := 2) (f := 2) h.1.1 (by decide) h.2

theorem isL3_centerQuotient_of_shapeL3 {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : ShapeL3 L) : IsL3 (↥L ⧸ Subgroup.center ↥L) 2 :=
  wccq_lieModel_centerQuotient (t := .PSL) (n := 3) (p := 2) (f := 2) h.1.1 (by decide) h.2

theorem isSp4_centerQuotient_of_shapeSp4 {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : ShapeSp4 L) : IsSp4 (↥L ⧸ Subgroup.center ↥L) 2 :=
  wccq_lieModel_centerQuotient (t := .PSp) (n := 2) (p := 2) (f := 2) h.1.1 (by decide) h.2

end CFSG.LocalAnalysis.WeakClosure81

end
