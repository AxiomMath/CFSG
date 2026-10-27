module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKMain
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKSchur
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKSz
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKL32
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepLeaf
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinDS
public import CFSG.Quasithin.Background.C22PfC
public import CFSG.Quasithin.Background.C2PushH129
public import CFSG.Quasithin.Background.E6TwentyThreeD
public import CFSG.Quasithin.Background.E6TwentyThreeE
public import CFSG.Quasithin.Background.HSL3Fix3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aA
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152Y20
public import CFSG.Quasithin.EmptyFaithful.S152Y21
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153F18C
public import CFSG.Quasithin.EmptyFaithful.S153IClose
public import CFSG.Quasithin.EmptyFaithful.SBd3L3
public import CFSG.Quasithin.EmptyFaithful.SBd4B1
public import CFSG.Quasithin.EmptyFaithful.SBd5Label
public import CFSG.Quasithin.EmptyFaithful.SBd6Close
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4
public import CFSG.Quasithin.H13.A5S136abP
public import CFSG.Quasithin.Vol2.Ch10SecALiftCore
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27C
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27F
public import CFSG.Quasithin.Vol2.Ch4Sec3L4312Two
public import CFSG.Quasithin.Vol2.Ch4Sec3L4313
public import CFSG.Quasithin.Vol2.Ch4Sec3L43Steps
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS2
public import CFSG.Quasithin.Vol2.KGFactLem1211G2
public import CFSG.RankThree.Classical.SteinbergBTNonsplitUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSUOuter
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import Certificates.Certificate8160

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N

theorem step829L3M22_noKantor (hmod : StmtFSUModule)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8)
    (hE22 : E2.E22StatementNoN) (hD3 : StmtD3L3M22) (hLU : HLU82)
    (hcard : CFSG.Quasithin.H.Mathieu.StmtH13Card)
    (hD4 : L829N.StmtD4L3M22) (hS3 : Step828Three) : Step829L3M22 :=
  step829L3M22_noKantor_of_leaves hmod h37 h38 h39 h3228 h325 h331 hC58 h317 h711n h825 h828 hE22
    hD3 hLU hcard hD4 hS3 nk_leafSz nk_leafSzDvd nk_leafU3Even nk_leafL3TwoOdd
    nk_leafL2Odd nk_leafL3Odd nk_leafU3Odd nk_leafL32 nk_leafSchurL32 nk_leafSL3Rep

end CFSG.Quasithin.H13.L829NK
