module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.List19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo


theorem exists_isLeviFamily_inf_blk {G : Type} [Group G] [Finite G] {M Dsub : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 Dsub)) (hlist : S19.List19_16_5 (BarInf Dsub))
    (hP : S19.IsNontrivialParabolic (Bar2 Dsub) (S19.barOfInter M Dsub))
    (hO : pCoreOf 2 Dsub ≤ M) :
    ∃ (d : ℕ) (L : Fin d → Subgroup G), IsLeviFamily (Dsub ⊓ M) d L ∧
      LeviAlt (Dsub ⊓ M) d L ∧
      LeviBlk (S19.IsLieTypeOver2 (BarInf Dsub))
        (∃ s, 6 ≤ s ∧ s ≤ 7 ∧ CFSG.Blueprint.LieModel (BarInf Dsub) .PSL s 2 1) d L :=
  exists_isLeviFamily_inf_leviBlk hq
    (hasLeviFamiliesBlk_of_list19 (isSimpleGroup_barInf hq) hlist) hP hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
