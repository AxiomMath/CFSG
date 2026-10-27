module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5a
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5b
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5c
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5e
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5f
public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam5g

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Hering129C

theorem kFCensus46Five_holds :
    KFCensus46Five := by
  intro Q Lb _ _ _ c a I X f hQ hD
  rcases hQ with ⟨s, hs, hQ⟩ | ⟨s, hs, hQ⟩
  · simp only [Sec4.sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kFCensus46Five_order Q Lb c a I X f ⟨.M11, by simp, hQ⟩ hD
    · exact kFCensus46Five_M12 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_order Q Lb c a I X f ⟨.M22, by simp, hQ⟩ hD
    · exact kFCensus46Five_order Q Lb c a I X f ⟨.M23, by simp, hQ⟩ hD
    · exact kFCensus46Five_M24 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_order Q Lb c a I X f ⟨.J1, by simp, hQ⟩ hD
    · exact kFCensus46Five_J2 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_J3 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_RuJ4 Q Lb c a I X f (Or.inr hQ) hD
    · exact kFCensus46Five_McL Q Lb c a I X f hQ hD
    · exact kFCensus46Five_order Q Lb c a I X f ⟨.HS, by simp, hQ⟩ hD
    · exact kFCensus46Five_He Q Lb c a I X f hQ hD
    · exact kFCensus46Five_RuJ4 Q Lb c a I X f (Or.inl hQ) hD
  · simp only [Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact kFCensus46Five_cover_M22 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_cover_J3 Q Lb c a I X f hQ hD
    · exact kFCensus46Five_cover_McL Q Lb c a I X f hQ hD
    · exact kFCensus46Five_cover_ON Q Lb c a I X f hQ hD

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
