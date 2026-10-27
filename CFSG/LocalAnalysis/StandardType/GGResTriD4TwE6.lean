module

public import CFSG.LocalAnalysis.StandardType.GGResTriD4TwE6Defs
public import CFSG.LocalAnalysis.StandardType.GGResTriD4TwE6Nbr
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResTriD4TwE6Input_of (hKG : GGTwE6TriD4RankKnown)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hRB : GGTwE6ThreeBstarRankInput) : GGResTriD4TwE6Input := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  exfalso
  obtain ⟨hcfg, -, hinn, -, hnb, -, -⟩ := hH
  rcases hP with hPL | hPK
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow⟩ := hPL
    exact ggTriD4_L_false hKG hRig hRB hcfg hinn.1 hnb hΛJ hΛX hJ hX hrow
  · obtain ⟨labJ, labX, hΛJ, hΛX, hJ, hX, hrow⟩ := hPK
    exact ggTriD4_K_false hKG hRig (ggNbrSubcomponentInput_of_lBalance hLB hSP) hRk hcfg hinn
      hnb hΛJ hΛX hJ hX hrow

end CFSG.StandardType

end
