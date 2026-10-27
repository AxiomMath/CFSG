module

public import CFSG.Blueprint.FischerDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7
open CFSG.Blueprint.Fischer

theorem localClass_eq_localSet {X : Type} [Group X] (E : Set X) (d : X) :
    LocalClass E d = localSet E d := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩

end CFSG.RankThree.PartOne.FIS
