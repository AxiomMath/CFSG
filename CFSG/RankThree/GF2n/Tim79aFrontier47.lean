module

public import CFSG.RankThree.GF2n.Tim79aFrontierFinal
import CFSG.RankThree.GF2n.Stroth78.Sec4SevenMain
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndMain

public section

namespace CFSG.RankThree.GF2n.Tim79a

section Certified


theorem tim79aStatementWCQ_of_noSqE1_parrott (h2 : OddTranspNoSqE1Dich)
    (hParrott : ParrottFi22Statement) : Tim79aStatementWCQ :=
  tim79aStatementWCQ_of_remaining_final h2 hParrott fun _ _ _ _ _ _ S _ _ h h217 h3 => by
    obtain ⟨α, hα⟩ := h.Tset_nonempty
    exact Stroth78.Sec4Seven.stroth78_47_of_psu42 S h h217 h3 hα
        (Stroth78.stroth78_47_psu42 S h h217 h3 hα)

end Certified

end CFSG.RankThree.GF2n.Tim79a
