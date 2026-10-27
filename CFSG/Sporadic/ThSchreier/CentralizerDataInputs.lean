
module

public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.BFS

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def centFixedIdx : List ℕ := natsOf (include_str "Data/CentFixedIndices.txt")

@[expose] def centImageIdx : List ℕ := natsOf (include_str "Data/CentImageIndices.txt")

@[expose] def centImageRows : List ℕ := hexsOf (include_str "Data/CentImagePlanes.txt")

@[expose] def centOrbitPar : List ℕ := natsOf (include_str "Data/CentOrbitParents.txt")

@[expose] def centOrbitLab : List ℕ := natsOf (include_str "Data/CentOrbitLabels.txt")

@[expose] def centOrbitEdges : List ℕ := natsOf (include_str "Data/CentOrbitEdges.txt")

end CFSG.Sporadic.ThSchreier
