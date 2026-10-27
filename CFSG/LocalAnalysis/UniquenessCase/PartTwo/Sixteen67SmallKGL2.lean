module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL2Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGL2Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

theorem k67BPrimeOneAt_psl2 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {p f : ℕ} (hp3 : p ≠ 3)
    (h : CFSG.Blueprint.LieModel ↥J .PSL 2 p f) : K67BPrimeOneAt Q J := by
  by_cases hp2 : p = 2
  · subst hp2
    exact k67BPrimeOneAt_psl2_even J hJ hC h
  · exact k67BPrimeOneAt_psl2_odd J hJ hC hp2 hp3 h

theorem k67CaseIIIAt_psl2 {Q : Type}
    [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) {p f : ℕ} (hp3 : p ≠ 3)
    (h : CFSG.Blueprint.LieModel ↥J .PSL 2 p f) : K67CaseIIIAt Q J := by
  by_cases hp2 : p = 2
  · subst hp2
    exact k67CaseIIIAt_psl2_even J hJ hC h
  · exact k67CaseIIIAt_psl2_odd J hJ hC hp2 hp3 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
