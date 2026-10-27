module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofCommon
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofQ
import CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof2127
public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127
public import CFSG.RankThree.PartTwo.Sec21.Item2119End7Proof2126
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2123
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofQ
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item2119EndProof Item2119End3Proof Item2119End4Proof

section Items


theorem item2119End_of_items9 (h211 : Item211) (h214 : Item214) (h215 : Item215)
    (h218 : Item218) (h2115 : Item2115) (h2116 : Item2116) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) (hLoc : Item2125StarLocal)
    (h2126 : Item2126Loc) (h2129S : Item2129S) (hEnd : Item2119EndLoc) : Item2119End :=
  have hStar : Item2125Star := item2125Star_of_local h45 h66 hLoc
  have hGen : Item2125Generic :=
    item2125Generic_of_star h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar
  item2119End_of_fix h211 h214 h215
    (item2123_of h211 h2115 h218 h2118 h45 h66 (item2123Field h45 h48 h66))
    (item2124_of h211 h2116 h45 h66)
    (item2125_of h211 h2116 h45 h66 (item2125Unique_of_generic h211 h2116 h45 h66 hGen) hGen)
    (item2126_of (item2126Torus_of h211 h2116 h45 h66 (item2126P_of_loc h2126)))
    (item2127_of_at h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar (item2127At_holds h45 h66))
    (item2127Q_of h211 h2116 h45 h66) (item2127QExtra_of h211 h2116 h45 h66) item2128
    (item2129Fix_of_loc (item2129Loc_of_s h2129S) (item2129Same_iff_endLoc.mpr hEnd))
    item2119FinalFix_holds

theorem item2119_of_steps9 (h211 : Item211) (h214 : Item214) (h215 : Item215)
    (h218 : Item218) (h2115 : Item2115) (h2116 : Item2116) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) (hΩ : Item2120Omega)
    (hLoc : Item2125StarLocal) (h2126 : Item2126Loc) (h2129S : Item2129S)
    (hEnd : Item2119EndLoc) : Item2119 :=
  item2119_of_items h211 h2115 h2116 h45 h66 hΩ
    (item2119End_of_items9 h211 h214 h215 h218 h2115 h2116 h2118 h45 h48 h66 hLoc h2126 h2129S
      hEnd)

end Items

end CFSG.RankThree.PartTwo.Sec21
