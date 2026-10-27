module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4T
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KX
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

theorem conf4212NoJ4_of6
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hOut : J4OutTrivial) (hBlk : J4BlockFacts) (hNC : J4L5BlockNotSelfDual)
    (hKX : J4KXNormal6) : Conf4212NoJ4 := by
  intro G _ _ T M L Mm I H K hy hIH c h6
  obtain ⟨I₂, -, hI₂LT, -, hy₂, hIH₂, c₂, h6₂⟩ := exists_le h37 h38 h39 hOut hBlk hy hIH c h6
  exact false_of_inner6 h37 h38 h39 hOut hBlk hKX hy₂ hIH₂ c₂ h6₂ hI₂LT
    (le_sup_pCoreOf hBlk hNC c₂ h6₂)

end NoJ4

end CFSG.Quasithin.H13.Ch4
