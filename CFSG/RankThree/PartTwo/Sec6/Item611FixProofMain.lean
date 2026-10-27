module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofG2
import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec21

section Certs

theorem item6_11_1Main_of_res2Fix (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (h641 : Item6_4_1) (hP : Item611UPlusOut)
    (hC : Item611ChooseMinus) (hF : Item611FieldL2T) (hG2 : Item611NotG2T)
    (hE81 : Item611NotE81T) : Item6_11_1Main := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA
  obtain ⟨E, hE, hEA, hLE⟩ := mem_lZeroUnion_iff.mp
    (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A c hL))
  obtain ⟨U, hU⟩ := h641 G hst E hE
  rcases Item211Res2Proof.mem_fourGroupsPlus_or_mem_fourGroupsMinus hE.1.2 hU with hUP | hUM
  · exact hP G hst A hA hrank c hcA hc1 L hL hCA E ⟨hE, hEA⟩ hLE U hUP
  · obtain ⟨c', hc'A, hc'1, L', hL', hCA', hL'E, R, hR, hRL, hRθ, -⟩ :=
      hC G hst A hA hrank c hcA hc1 L hL hCA E ⟨hE, hEA⟩ U hUM
    rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hc'A hc'1 hL' hCA' with
      h | h | ⟨hdec, hcL, h⟩ | h
    · exact hF G hst A hA hrank c' hc'A hc'1 L' hL' hCA' E ⟨hE, hEA⟩ hL'E R hR hRL hRθ h
    · exact hE81 G hst A hA hrank c' hc'A hc'1 L' hL' hCA' E ⟨hE, hEA⟩ hL'E R hR hRL hRθ
        (Or.inl h)
    · rcases h with h | h
      · exact hG2 G hst A hA hrank c' hc'A hc'1 L' hL' hCA' E ⟨hE, hEA⟩ hL'E R hR hRL hRθ hdec
          hcL h
      · exact hE81 G hst A hA hrank c' hc'A hc'1 L' hL' hCA' E ⟨hE, hEA⟩ hL'E R hR hRL hRθ
          (Or.inr ⟨hdec, hcL, h⟩)
    · exact item611NotG2CoverT_holds G hst A hA hrank c' hc'A hc'1 L' hL' hCA' E ⟨hE, hEA⟩ hL'E
        R hR hRL hRθ h

end Certs

end CFSG.RankThree.PartTwo.Sec6
