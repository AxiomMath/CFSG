module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneMainE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenL1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem compose17_final
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (r1 : R17_1At D V₀ V hV)
    (r2 : R17_2At D V₀ V hV) (r3 : R17_3At D V₀ V) (r6 : R17_6At D V₀ V) (r17 : R17_17At D V₀ V)
    (r33_2 : R17_33_2At D V₀ V) (r42 : R17_42At D V₀ V) (h109 : Inputs1719.UC2_10_9 D)
    (h127 : R127 D) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (hW143 : Inputs1719.W4Thm14_3) (hSg : UC6S846.SigmaStd D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h638 : UC6.R6_38 D)
    (h76 : F07.R76 D) (h63 : UC6.R6_3 D) (h614 : UC6.R6_14 D) (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (h8100 : CFSG.Open.evenRank G ≠ 3 → F08.R8100R D) (h13s : SigmaRankThree13 D)
    (h869 : F08.R869 D) (h69 : UC6.R6_9 D)
    (h1219 : D.sig = D.sig1) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h136 : R136a D)
    (h8107 : F08.R8107 D) (h148 : Inputs1719.R14_8 D) (h82 : F08.R82 D) :
    R17_57At D V₀ V ∧ R17_64_1At D V₀ V ∧ R17_64_2At D V₀ V ∧ R17_64_3At D V₀ V ∧
      R17_65At D V₀ V ∧ R17_67At D V₀ V ∧ R17_68At D V₀ V := by
  obtain ⟨-, r2_2, r2_3, -, r2_5⟩ := id r2
  have r55 : R17_55At D V₀ V :=
    seventeen_fiftyfive D h109 h127 hx h61 h126 h111 hW143 hSg hV r3 r1
  have r56 : R17_56At D V₀ V :=
    seventeen_fiftysix D V₀ V hThin hCyc h638 r33_2
  have r57 : R17_57At D V₀ V :=
    seventeen_fiftyseven D V₀ V hV hSg hThin hCyc h638 r33_2 r2_2 r2_3 r2_5 r55
  have r59 : R17_59At D V₀ V :=
    seventeen_fiftynine D hSg h76
  have r60 : R17_60At D V₀ V :=
    seventeen_sixty D hSg r57 (fun _ => r1) hThin hCyc h638 r33_2 (fun _ => r2_2) (fun _ => r2_3)
  have r61 : R17_61At D V₀ V :=
    seventeen_sixtyone D hV hThin r3 r55 r56 r57 r60 h63 h76 h614 hK35 h72 h8100 hSg h13s
  have r62 : R17_62At D V₀ V :=
    seventeen_sixtytwo D hSg h614 r61 r59 h869 h63 h69 hThin
  have r63 : R17_63At D V₀ V :=
    seventeen_sixtythree D r62 (fun _ => r1) r6.2.1 r17 r33_2 hThin
  have r58 : R17_58At D V₀ V :=
    seventeen_fiftyeight D hV r61 r63
  have r64_1 : R17_64_1At D V₀ V :=
    seventeen_sixtyfour_one D hV h1219 h1669 h136 r2_2 r2_3 r3 r6.1 r6.2.2 r17 r33_2 r55 r57 r58
      hCyc
  have r64_2 : R17_64_2At D V₀ V :=
    seventeen_sixtyfour_two D hV h1219 h1669 h136 r2_2 r2_3 r3 r6.1 r6.2.2 r17 r33_2 r55 r57 r58
      hCyc
  have r64_3 : R17_64_3At D V₀ V :=
    seventeen_sixtyfour_three D hV h1219 h1669 h136 r2_2 r2_3 r3 r6.1 r6.2.2 r17 r33_2 r55 r57 r58
      hCyc
  have r65 : R17_65At D V₀ V :=
    seventeen_sixtyfive D r42 r64_1 r64_2 r64_3
  have r67 : R17_67At D V₀ V :=
    seventeen_sixtyseven hV r42 h109 h869 hSg h638 h72 hK35
  have r68 : R17_68At D V₀ V :=
    seventeen_sixtyeight hV r1 r3 r2_2 r2_3 r33_2 r42 r55 r57 r64_1 r64_2 r64_3 hThin hCyc h638
      hSg hx h82
  exact ⟨r57, r64_1, r64_2, r64_3, r65, r67, r68⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
