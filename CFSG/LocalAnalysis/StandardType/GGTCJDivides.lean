module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import CFSG.LocalAnalysis.StandardType.GGTCJDivUni
public import CFSG.LocalAnalysis.StandardType.GGTCJDivSymp
public import CFSG.LocalAnalysis.StandardType.GGTCJDivOrth
public import CFSG.LocalAnalysis.StandardType.GGTCJDivExc

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem tcj_inn_of_families_all (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S)
    (J : Subgroup S) (labK labJ : GLALabel) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) :
    (canonLabel labK).n ∣ (canonLabel labJ).n := by
  rcases fam_cover labK with h | h | h | h | h
  · exact innDiagAllLin S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact innDiagAllUni S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact innDiagAllSymp S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact innDiagAllOrth S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ
  · exact innDiagAllExc S p α J labK labJ h hp hp2 hcen hin hα hlabJ hJ

end CFSG.StandardType.TCJ

end
