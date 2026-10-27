module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

@[expose] noncomputable def w3 : WeylGroup .E6 := (coxeterSystem .E6).wordProd e6ThreeWord

end CFSG.StandardType.GGKG3
