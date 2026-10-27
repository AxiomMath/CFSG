module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.AdapterFour
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

open Subgroup CFSG.Yardstones.Mf4cdcdf2e013

variable {G : Type} [Group G] [Finite G]

theorem theorem1669At_of_thm1669 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (h : Thm1669 (UC6.dataOfSetup4 hS hU S)) : Theorem1669At S.M S.T := by
  intro V₀ V H₀ h123Y hH h124 hcard
  have h123' : UC22.Hyp123 S.M S.T V₀ V :=
    (hyp123_iff S.maxLocal S.T V₀ V).1 h123Y
  have hV : UC22.InCalV S.M V := inCalV_of_hyp123 h123'
  have hMBar : UC22.MBarGT S.M V₀ V 3 :=
    h V₀ V ⟨h123', H₀, hH, h124⟩ hcard
  exact minCodimGt_of_mBarGT
    (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hV.2.2.2 ha hb) hV.2.2.1 hMBar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four
