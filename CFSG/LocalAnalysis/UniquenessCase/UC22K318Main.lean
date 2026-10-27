module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22K318Low
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open CFSG.RankThree.SubgroupLists (MitchellPartThree)


theorem k318s_of_mitchell (hIII : MitchellPartThree) : UCK.K318s := by
  intro G _ _ _ hperf hO2 hsimple hrank hcent
  haveI : Group.IsPerfect G := ⟨hperf⟩
  have hXs : Group.IsSolvable (CFSG.solvableRadical G) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  obtain ⟨q, _, hq2, -, hl | ⟨φ, hφ, hirr, hcs⟩⟩ :=
    classification_or_irreducible_four (CFSG.solvableRadical G) hXs hO2 hrank hcent hsimple
  ·
    obtain ⟨h1, h2⟩ := k318_of_list (Fact.out : q.Prime) hq2 hl
    refine ⟨?_, fun hA => Or.inr (h2 hA)⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  ·
    obtain ⟨h1, h2⟩ := k318s_of_irreducible_four hIII hXs hsimple hq2 (hrank q Fact.out hq2) hφ
      hirr hcs
    exact ⟨h1, fun _ => Or.inl h2⟩

theorem k318_of_mitchell (hIII : MitchellPartThree) : UCK.K318 :=
  UCK.K318_of_K318s (k318s_of_mitchell hIII)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
