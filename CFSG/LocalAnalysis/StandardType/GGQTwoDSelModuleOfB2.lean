module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSelModule
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.StandardType.QTwo

section Input


theorem ggQTwoDSelModuleInputOn_of_selectedModule {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGQTwoDSelModuleInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  obtain ⟨hrc, ht, hns, hpres, r, hr, hrc', h6⟩ := hcfg
  have hp : p = 3 := ggQTwo_p_eq_three hrc M e hpres hr hrc' h6
  subst hp
  exact ggQTwoD_selectedModule hTBF hWI ⟨hrc, ht, hns, hpres, r, hr, hrc', h6⟩ e' (hR m hm) hM

theorem ggQTwoDSelModuleInput_of_selectedModule (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoDSelModuleInput :=
  ggQTwoDSelModuleInputOn_of_selectedModule (fun m hm => by omega) hTBF hWI

end Input

end CFSG.StandardType.QTwo

end
