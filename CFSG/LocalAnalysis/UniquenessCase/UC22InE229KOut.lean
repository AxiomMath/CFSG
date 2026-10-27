module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Centralizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2qOddAut
import CFSG.RankThree.PartTwo.Sec18.Item189ListEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KBridge

theorem kOddOutInner_holds : KOddOutInner := by
  intro Q _ _ hQ θ hθ
  rcases hQ with ⟨k, -, hL⟩ | ⟨q, hq, hq5, hL⟩ | hJ
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))
    refine CFSG.OddStandard.AltStdSec.SwapPartner.mem_inner_of_coprime_orderOf_outer ?_
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      CFSG.RankThree.PartTwo.Sec18.card_outer_projSL_two Nat.one_le_two_pow]
    exact hθ.coprime_two_right.pow_right k
  · haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.mulAut_odd_inner_of_isPSL (by omega) (by omega)
      (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)) θ hθ
    exact ⟨g, hg.symm⟩
  · obtain ⟨x, hx⟩ := (kJ1_holds Q hJ).2.2 θ
    exact ⟨x, hx.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KBridge
