module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.KF148SigONE27Proof
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section ON

theorem step148KThetaON_holds : Step148KThetaON := by
  intro G _ _ A c L h Y hY _ hYB B Q e K Le hP _ _ _ _ _ _ _ hON3
  have hLe : Le ∈ thetaComponentsAt 3 e := hP.2.2.2.2.2.2.2.2.1
  obtain ⟨X, _, _, P, H, hXp, hXT, hPE, hPN, hHp, hHq, hgen, ⟨ψ⟩⟩ :=
    ONLoc.exists_e27_data (Res7Sig.sig148_of_isPoint148 h hYB hP) hON3
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe)
      (fun x hx3 hxA => Sec4.mem_of_maximal_of_commute h.maximal_isElemAbelian hx3 hxA)
  obtain ⟨h7, ⟨φ⟩⟩ := Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.kf148SigONE27_holds X hXp
    hXT P H hPE hPN hHp hHq hgen
  exact Or.inr ⟨h7, ⟨ψ.symm.trans φ⟩⟩

end ON

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
