module

public import CFSG.RankThree.GF2n.Stroth80.Sec53FromFix
public import CFSG.RankThree.GF2n.Stroth80.Sec53Odd
public import CFSG.RankThree.GF2n.Stroth80.Sec53aVoneNe

public section

namespace CFSG.RankThree.GF2n.Stroth80


theorem sec53CentralizerW1_of_fix (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hB : Stroth53FixBStatement) (hC : Stroth53FixCStatement) :
    Sec53CentralizerW1Statement :=
  sec53CentralizerW1_of_vone_ne h34 hRoot h51
    (vone_ne_of_odd h34 hRoot h51 (stroth53Odd_holds h34 hRoot h51)
      (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ => hB G M Q Z B hc n t hs hsp r hr hplane)
      (fun G _ _ M Q Z B hc n t hs hsp r hr hplane _ => hC G M Q Z B hc n t hs hsp r hr hplane))

end CFSG.RankThree.GF2n.Stroth80
