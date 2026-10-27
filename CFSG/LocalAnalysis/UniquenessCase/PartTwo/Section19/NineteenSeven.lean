module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenCaseTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


theorem nineteen_seven_of_gap (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h2 : R19_2At D V₀ V p L K h) (h3 : R19_3At D V₀ V p L K h)
    (h5 : R19_5At D V₀ V p L K h) (h1310 : Inputs1719.W4Thm13_10) (h1513 : R15_13 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hgap : Gap19_7_SingleComponent) :
    R19_7At D V₀ V p L K h := by
  by_contra hm
  have hV := h.hyp.isElemAbelian
  obtain ⟨hS, hi | hii⟩ :=
    nineteen_seven_thirteen_ten D h hV h2 h5 hx h61 h127 h1214 h1310 hgap hm
  · exact nineteen_seven_case_one D hV hS h3 h5 h61 hSg h1219 h1513 hi
  · exact nineteen_seven_case_two D hV hS h2 h3 h5 hx h61 h126 h127 hSg h1219 hii

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
