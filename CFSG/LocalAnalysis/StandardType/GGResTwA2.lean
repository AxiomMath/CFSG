module

public import CFSG.LocalAnalysis.StandardType.GGResTwA2Defs
public import CFSG.LocalAnalysis.StandardType.GGResTwA2Nbr
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTwA2Input_of (hKG : GGTwE6TwA2CompKnown)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hRB : GGTwE6ThreeBstarRankInput) : GGResTwA2Input := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  exfalso
  obtain ⟨hcfg, -, hinn, -, hnb, -, -⟩ := hH
  rcases hP with hPL | hPK
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow⟩ := hPL
    exact ggTwA2_L_absurd hKG hRig hRB hcfg hinn.1 hrow.2.2.1 hnb hΛJ hΛX hJ hX hrow
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow⟩ := hPK
    exact ggTwA2_K_absurd hKG hRig (ggNbrSubcomponentInput_of_lBalance hLB hSP) hRk hcfg hinn
      hrow.2.2.1 hnb hΛJ hΛX hJ hX hrow

end CFSG.StandardType

end
