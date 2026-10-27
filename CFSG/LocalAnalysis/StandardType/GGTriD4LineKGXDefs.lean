module

public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def triD4LineV : WeylGroup Tag.D4 := (coxeterSystem Tag.D4).wordProd [0, 2, 1, 3]

end CFSG.StandardType
