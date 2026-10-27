module

public import CFSG.Quasithin.Vol2.Asc94.HeK4
public import CFSG.Quasithin.Vol2.Asc94.TSF6Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Check
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIICheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step11
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.Quasithin.A94

open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.AS81

theorem asc94K_of_he42_step11
    (hOrd : He_order) (h11 : Step11) (hHe : He42) :
    CFSG.Quasithin.H13.Asc94_M24He_L52TypeK :=
  asc94K_of_typeSplit L52.f6Model_holds
      (heCaseIIK_of_he42 HypII.l34_checkE16 h11 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34
          HypII.hypII_L34 hHe) hOrd

theorem asc94K_of_he42'
    (hOrd : He_order) (hHe : He42) : CFSG.Quasithin.H13.Asc94_M24He_L52TypeK :=
  asc94K_of_he42_step11 hOrd
    (step11_of RankTwoFoundation.lemma32 RankTwoFoundation.lemma33Three) hHe

end CFSG.Quasithin.A94
