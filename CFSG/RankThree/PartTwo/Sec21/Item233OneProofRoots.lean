module

public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofHull
public import CFSG.RankThree.PartTwo.Sec21.Item231Of
import CFSG.RankThree.PartTwo.Sec21.Item229Pre
import CFSG.RankThree.PartTwo.Sec21.Item233Skeleton
public import CFSG.RankThree.PartTwo.Sec21.Item232
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem item233KLeComponent_of (h231 : Item231) (hstar : Item231IStar) (h232 : Item232)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hR : TerminalRootComponents) :
    Item233KLeComponent := by
  intro G _ _ A E U c L hpair B hBA hB3 X hX
  have hK := hKW G A E U c L hpair
  have hAI : A ≤ iGroup A := (h232 G A E U c L hpair).1
  obtain ⟨φ, hφ, hP⟩ := hR G (iGroup A) A hAI hpair.mem_S.1.1
    (terminal_of_item231Concl (h231 G A E U c L hpair)) (dStar A) (fun φ hφ => hφ.1)
    (fun g hg φ hφ => conj_mem_dStar_of_mem_wStar (starOf_le_wStar A _ hg) hφ)
    (hstar G A E U c L hpair).symm B hBA hB3 X hX
  obtain ⟨n, hn, ⟨e⟩⟩ := Item233One.exists_two_le_mulEquiv_kOf h222 hpair hφ
  exact ⟨φ, hφ, hP (kOf A φ) (kOf_le_iGroup hφ)
    ((kOf_le_kZero hK hφ).trans (kZero_le_centralizer A φ)) (isPerfect_of_mulEquiv_projSL hn e)⟩

end CFSG.RankThree.PartTwo.Sec21
