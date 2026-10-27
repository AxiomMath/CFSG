module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4LocalDefs
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Clauses3
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Clause12

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

section Holds

theorem kf_F4Local'_holds : KF_F4Local' := by
  intro X _ _ Y hY
  obtain ⟨e⟩ := exists_model_zmod hY
  exact ⟨clause_center e, fun g hg hout => ⟨clause_outer_one e hg hout, clause_outer_two e hg hout⟩,
    clause_order3 e, clause_Syl2 e, clause_lines e, clause_unique_E81 e, clause_inv_order3 e,
    clause_K12 e, clause_Z_fusion e, clause_O2 e⟩

end Holds

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
