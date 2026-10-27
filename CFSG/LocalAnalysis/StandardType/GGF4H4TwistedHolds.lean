module

public import CFSG.LocalAnalysis.StandardType.GGF4H4TwistedAux1
import CFSG.LocalAnalysis.StandardType.GGF4H4TwistedOrder
import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64TwHolds
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.StandardType

theorem ggF4H4Twisted_of_balance
    (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hP : GGStdSubPrimeInput) : GGF4H4Twisted := by
  intro G _ _ p B Bs x L D J ks hres hB f hf hpf hLlab hJB K hK hlist
  rcases ggF4TW_twistedNbrLabel hL hRig hTCJ hP ggF4TW_orderInput_holds
      (ggF4H4Psl64Twisted_of_balance hL hRig) hres hB hf hpf hLlab hJB hK hlist with
    hC | hD
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, hpf, hLlab, hC⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hpf, hLlab, hD⟩)))

end CFSG.StandardType

end
