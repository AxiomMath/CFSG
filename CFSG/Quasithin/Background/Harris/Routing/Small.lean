module

public import CFSG.Quasithin.Background.Harris.L2.Main
public import CFSG.Quasithin.Background.Harris.L2.Natural
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinus
public import CFSG.Quasithin.Background.Harris.L2.Steinberg8
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.ModelConversions
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.Module
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Quasithin.Background.Harris.OrdinaryProofs

theorem oneCompFor_famAlt5 : OneCompFor (FamAlt 5) :=
  (L2.oneCompFor_famL2_of_cases L2.case6_holds L2.case7_holds L2.case16_holds).mono fun X _ h => famL2_of_famAlt5 X h

theorem oneCompFor_famAlt8_of (hL4 : OneCompFor (FamLn2 4)) : OneCompFor (FamAlt 8) :=
  hL4.mono fun X _ h => famLn2_four_of_famAlt8 X h

theorem oneCompFor_famOddL2Small_of (hL3 : OneCompFor FamL3)
    (hA6 : OneCompFor (FamAlt 6)) : OneCompFor FamOddL2Small := by
  intro V _ _ _ Γ A L m hs hL
  rcases famL2_or_famL3_or_famAlt6_of_famOddL2Small ↥L hL with h | h | h
  · exact L2.oneCompFor_famL2_of_cases L2.case6_holds L2.case7_holds L2.case16_holds V Γ A L m hs h
  · exact hL3 V Γ A L m hs h
  · exact hA6 V Γ A L m hs h

end CFSG.Quasithin.G11.Harris
