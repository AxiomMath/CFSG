module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.StandardType

namespace TwF4SUThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem ggTwF4ThreeRankInput_holds :
    TableBExcSmallRanks.GGTwF4ThreeRankInput := by
  intro a _ K _ _ _ hK E hE
  have h9 :=
    CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma a K hK E hE
  omega

end TwF4SUThree

end CFSG.StandardType
