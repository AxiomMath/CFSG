module

public import CFSG.RankThree.GF2n.Stroth80.Sec7OutSolvableExtra
public import CFSG.LieType.Catalog.Realization
public import CFSG.LocalAnalysis.StandardType.GGSkeleton

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem outSolvableRankTwo_holds : OutSolvableRankTwoStatement := by
  intro X _ _ hX hnonab P hP
  rcases hX with ⟨m, -, h⟩ | ⟨m, -, h⟩ <;>
  · haveI : IsSimpleGroup X := (CFSG.LieType.Catalog.lieModel_finite_simple X _ _ _ _ h).2.2
    exact perfect_action_inner_of_catalog X hnonab
      (CFSG.StandardType.inCatalog_of_lieModel_std X h) P hP

end CFSG.RankThree.GF2n.Stroth80
