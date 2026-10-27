module

public import CFSG.RankThree.PartTwo.Sec21.FF79Assembly
public import CFSG.RankThree.PartTwo.Sec21.FF79Reduce5
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13b
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CKLor
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42DihD
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NHolds
public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaQ
public import CFSG.RankThree.PartTwo.Sec21.FF84KF1Holds
public import CFSG.RankThree.PartTwo.Sec21.FF84KSOutHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Result

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem ff79_1_4_of_centAlpha
    (hCA : FF79KCentAlpha) : FF79_1_4 :=
  ff79_1_4_of ff79KTypeLn_holds ⟨ff79KCenterJ_holds, ff79KAutCentP_holds, hCA⟩

theorem ff79_4_1_of_centAlpha
    (hCA : FF79KCentAlpha) : FF79_4_1 :=
  ff79_4_1_of ff79KTypeLn_holds ⟨ff79KCenterJ_holds, ff79KAutCentP_holds, hCA⟩

theorem ff79_4_2Pre_of_centAlpha
    (hCA : FF79KCentAlpha) : FF79_4_2Pre :=
  ff79_4_2Pre_of' (ff79_4_2KLor_of (ff79_1_3_of ff79KTypeLn_holds ff79KTypeLnNorm_holds
      ff79KGL33_holds) (ff79_1_4_of_centAlpha hCA)
      (ff79_4_1_of_centAlpha hCA))
    ff79LemmaN_holds (FF84.lemmaQ_of FF84.ff84KF1_holds FF84.ff84KSOut_holds) (ff79_1_3_of ff79KTypeLn_holds ff79KTypeLnNorm_holds
        ff79KGL33_holds) (ff79_1_4_of_centAlpha hCA)
    (ff79_4_1_of_centAlpha hCA)

theorem ff79_4_3_of_centAlpha
    (hCA : FF79KCentAlpha) : FF79_4_3 :=
  ff79_4_3_of (ff79_1_3_of ff79KTypeLn_holds ff79KTypeLnNorm_holds ff79KGL33_holds) (ff79_1_4_of_centAlpha hCA) (ff79_4_1_of_centAlpha hCA)
    (ff79_4_2Pre_of_centAlpha hCA)

theorem ff79_4_2_of_centAlpha
    (hCA : FF79KCentAlpha) : FF79_4_2 :=
  ff79_4_2_of (ff79_1_4_of_centAlpha hCA) (ff79_4_1_of_centAlpha hCA)
    (ff79_4_2Pre_of_centAlpha hCA) (ff79_4_3_of_centAlpha hCA)

theorem ff79Extraspecial_of_thmA5
    (hCA : FF79KCentAlpha) (hA : FF79TheoremA_simpleK5) :
    FF79Extraspecial :=
  ff79Extraspecial_of5 (ff79_1_3_of ff79KTypeLn_holds ff79KTypeLnNorm_holds ff79KGL33_holds) hA (ff79_4_3_of_centAlpha hCA)
    (ff79_4_4X_of_lemmas (ff79_4_1_of_centAlpha hCA) (ff79_4_2_of_centAlpha hCA)
      (ff79_4_3_of_centAlpha hCA))

end CFSG.RankThree.PartTwo.Sec21.FF79
