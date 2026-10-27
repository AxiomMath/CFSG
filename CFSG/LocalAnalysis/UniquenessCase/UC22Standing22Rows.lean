module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem Standing22.r613ident {D : Data G} (hs : Standing22 D) : UC6.R613Ident D :=
  uc22p22q_r613ident_of D hs.sigma23 hs.r6_1 hs.sigma2

theorem Standing22.r613aut {D : Data G} (hs : Standing22 D) : UC6.R613Aut D :=
  uc22p22q_r613aut_of D hs.sigma23 hs.r6_1 hs.sigma2 hs.cent

theorem Standing22.r6_13 {D : Data G} (hs : Standing22 D) : UC6.R6_13 D :=
  uc22p22q_r6_13_of_print D hs.sigma23 hs.r6_1 hs.sigma2 hs.r613ident hs.cent hs.r613aut

theorem Standing22.r111 {D : Data G} (hs : Standing22 D) : F11.R111 D :=
  uc22p22q_r111_of D hs.sigma23 hs.r6_1 hs.r6_11

theorem Standing22.r112 {D : Data G} (hs : Standing22 D) : F11.R112 D :=
  uc22p22q_r112_of D hs.sigma23 hs.r6_1 hs.sigma2 hs.r613ident hs.cent hs.r613aut

theorem Standing22.sig_eq_sig1 {D : Data G} (hs : Standing22 D) (h126 : PartTwo.R126 D)
    (h127 : PartTwo.R127 D) (h1211 : PartTwo.R1211_1 D) (h111 : PartTwo.W3Thm111 G)
    {V₀ V : Subgroup G} (h : PartTwo.Hyp125 D V₀ V) : D.sig = D.sig1 :=
  PartTwo.twelve_nineteen D hs.sigma23 hs.r6_1 hs.r6_13 hs.hyp612 hs.r111 hs.r112 h126 h127
    h1211 h111 h

theorem Standing22.r119 {D : Data G} (hs : Standing22 D) (h77 : F07.R77Eq D)
    (h869 : F08.R869 D) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) : F11.R119 D :=
  PartTwo.ElevenNine.r119_holds D hs.sigmaStd hs.r6_1 hs.r6_3 h77 h869 hs.r111 hs.r112 hThin hCyc

end CFSG.LocalAnalysis.UniquenessCase.UC22
