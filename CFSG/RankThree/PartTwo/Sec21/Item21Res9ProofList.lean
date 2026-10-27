module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res8ProofSylowList
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofON
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofMcL
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofJ3
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofG23
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofU43
public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item21Res9Proof

section Certs


theorem kF2110SylowNoncentralList_holds : KF2110SylowNoncentralList := by
  intro X _ _ hq h3Z h27 hfam S
  rcases hfam with ⟨p, e, hp, he, hL⟩ | hG2 | ⟨⟨hU⟩⟩ | ⟨⟨hJ3⟩⟩ | ⟨⟨hMcL⟩⟩ | ⟨⟨hON⟩⟩
  · exact exists_noncentral_L3 he hL h27 S
  · exact exists_noncentral_G23 hG2 S
  · exact exists_noncentral_U43 hU S
  · exact exists_noncentral_J3 hJ3 S
  · exact exists_noncentral_McL hMcL S
  · exact exists_noncentral_ON hq h3Z hON S

theorem kF2110SylowNoncentral_of_res9 (h43 : Sec4.Item4_3) (h41 : Sec4.Item4_1LargePrime) :
    KF2110SylowNoncentral :=
  kF2110SylowNoncentral_of (kF2110SylowNoncentralBig_of h43 h41 kF2110SylowNoncentralList_holds)

end Certs

end CFSG.RankThree.PartTwo.Sec21
