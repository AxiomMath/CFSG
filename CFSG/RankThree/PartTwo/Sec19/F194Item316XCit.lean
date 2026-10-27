module

public import CFSG.RankThree.PartTwo.Sec19.F194Item316X
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LeavesTwoK
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec19



theorem item316ScriptX_of_cit
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie)
    (hGH : SectionalTwoRankFourCatalog) : Item316ScriptX := by
  have hNA := CFSG.CGT.PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz hCIT hL
    CFSG.CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate
  have h := CFSG.AGLEmbeddingD2.aschbacherTwoK_solomonK_of_remaining
    CFSG.CGT.A8S.a8SylowInput hNA
  exact item316ScriptX_of_kforms
    CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved h.1 h.2 hGH

end CFSG.RankThree.PartTwo.Sec19
