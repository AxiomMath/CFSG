module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec15.Notation
import CFSG.Certificates.Kernel.M12SigCoset

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_pair {x y g : G} :
    g ∈ Subgroup.centralizer ({x, y} : Set G) ↔
      g ∈ Subgroup.centralizer ({x} : Set G) ∧ g ∈ Subgroup.centralizer ({y} : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
