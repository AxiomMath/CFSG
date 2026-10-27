module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLMark
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Plain

theorem ggNbrKGFieldG2Three_plain (lab : LargeEvenLabel) (ht : lab.tag = .G2) :
    LargeEvenLabelAll lab (fun R _ I _ => GGTorusNoLineComp 3 2 R I) :=
  LargeEvenLabelAll.mono
    (fun _ _ _ _ h => ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_card_lt h))
    (NbrInnerNine.largeEvenLabelAll_card_lt_G2_all (p := 3) Nat.prime_three (by norm_num) ht)

theorem ggNbrKGFieldG2Three_of_off (h : GGNbrKGFieldG2ThreeOff) : GGNbrKGFieldG2Three := by
  intro lab hl ht h6
  refine LargeEvenLabelAll.mono ?_
    (largeEvenLabelAll_and (ggNbrKGFieldG2Three_plain lab ht) (h lab hl ht h6))
  rintro R _ I F ⟨h1, h2⟩ hs hna
  exact ⟨h1, h2 hs hna⟩

end Plain

end CFSG.StandardType

end
