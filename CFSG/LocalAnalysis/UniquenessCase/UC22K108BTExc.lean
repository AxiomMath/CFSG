module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108Rows
public import CFSG.Milestones.ASVolI.A3Aut.SBG2
public import CFSG.Milestones.ASVolI.A3Aut.SBD4
public import CFSG.Milestones.ASVolI.A3Aut.SBF4
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Blueprint (LieModel)

theorem k108BTSz_holds : K108BTSz := by
  intro S _ _ _ _ ⟨_, _, h⟩ T hT H hTH hH
  exact uc22p2214_solvBorel_Sz h hT hTH hH

section Exceptional


theorem k108BTG2_holds : K108BTG2 := by
  intro S _ _ _ _ ⟨n, hn, h⟩ T hT H hTH hH
  exact CFSG.ASVolI.burnsideAut_solvBorel_G2 S n hn.le (h.chevalleyExceptionalModel (by decide)) T
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT) H hTH hH

theorem k108BT3D4_holds : K108BT3D4 := by
  intro S _ _ _ _ ⟨n, hn, h⟩ T hT H hTH hH
  exact CFSG.ASVolI.burnsideAut_solvBorel_3D4 S n hn (h.chevalleyExceptionalModel (by decide)) T
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT) H hTH hH

theorem k108BT2F4_holds : K108BT2F4 := by
  intro S _ _ _ _ ⟨n, hn, h⟩ T hT H hTH hH
  have hR := (h.reeTitsModel (by decide)).2
  obtain ⟨a, ha, -⟩ := hR.2
  exact CFSG.ASVolI.burnsideAut_solvBorel_2F4 S n ⟨a, ha⟩ hn hR T
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT) H hTH hH

end Exceptional

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
