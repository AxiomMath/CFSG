module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofLower
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofONGen
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProof
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProof
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG.RankThree.PartTwo.Sec13

theorem item142AllS14_of_res2 (h1 : Concl142S14) (h131 : Item131) (hspor : SporadicModels131)
    (hKer : Step142PGLKer) (hGen : Step142LowerGen) (hIdx : Step142L34Index)
    (h3 : Step142TypesS14) : Item142AllS14 :=
  item142AllS14_of h1 (step142LowerS14_of hGen hIdx) (step142UpperPGLS14_of h131 hspor hKer) h3

theorem item142AllS14_of_res3 (h1 : Concl142S14) (h131 : Item131) (hspor : SporadicModels131)
    (hKer : Step142PGLKer) (hGen : Step142LowerGen) (hIdx : Step142L34Index)
    (hT1 : Step142TypesOne) (hT2 : Step142TypesM22) (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_res2 h1 h131 hspor hKer hGen hIdx (step142TypesS14_of hspor hT1 hT2 hT3)

theorem item142AllS14_of_leaves2
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hKer : Step142PGLKer) (hGen : Step142LowerGen)
    (hIdx : Step142L34Index) (hT1 : Step142TypesOne) (hT2 : Step142TypesM22)
    (hT3 : Step142TypesHJ) : Item142AllS14 :=
  item142AllS14_of_res3 (concl142S14_of_res h131 h134 h48 h422 h45 hKer) h131
    Sec13.sporadicModels131 hKer hGen hIdx hT1 hT2 hT3

theorem step148PointHJ_of_res2
    (h143 : Concl143S14) (h134 : Item134) (h48 : Sec4.Item4_8) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h142 : Item142AllS14) (hΩ : Step148PointOmega)
    (hD : Step148PointHJdONGenD) : Step148PointHJ :=
  step148PointHJ_of_res h143 h134 h48 (step148PointHJdONGen_of h422 h45 h142 hΩ hD)

end CFSG.RankThree.PartTwo.Sec14
