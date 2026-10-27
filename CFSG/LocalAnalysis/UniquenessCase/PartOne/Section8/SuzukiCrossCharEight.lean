module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiCrossCharBorel
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBMSuzukiEightCover
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Submodule

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Simplicity
open CFSG.LocalAnalysis.ComponentInitial.SuzukiEightCover
open CFSG.RankThree.PartTwo.KFacts.LandazuriSeitzProof
  (exists_common_eigenvector linearIndependent_of_eigen natCard_le_finrank)

open scoped commutatorElement IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
