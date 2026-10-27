module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure s16h_Std (D : Data G) : Prop where
  hx : DataExt D
  hSig : UC6S846.SigmaStd D
  h61 : UC6.R6_1 D
  h63 : UC6.R6_3 D
  h77 : F07.R77Eq D
  h82 : F08.R82 D
  h869 : F08.R869 D
  h111 : F11.R111 D
  h112 : F11.R112 D
  h119 : F11.R119 D
  hThin : ThinList13
  hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian
  h127 : R127 D
  h126 : R126 D
  h1211 : R1211_1 D
  h111W : W3Thm111 G
  h6161ii : W3Lem616_1ii G

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
