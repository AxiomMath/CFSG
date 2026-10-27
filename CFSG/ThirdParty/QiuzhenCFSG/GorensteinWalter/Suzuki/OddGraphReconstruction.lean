module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.UConjugatesGraph
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphOrbitals
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphIntersection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphFirstRow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphIntersectionArray
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphStarAction

namespace CFSG
end CFSG
open CFSG

/-!
# Odd-graph reconstruction for the Suzuki first case

This is the architecture boundary for the `R9` recognition route.  The
clean 35-point commuting graph (`UConjugatesGraph`) is the intended source
of the index-seven subgroup.  The coset-layer and neighbour modules
(`OddGraphLayers`, `OddGraphNeighbors`) already provide the
`G ⧸ Ĥ ≃ UConjugates c` identification and the rooted layer counts; the
root bridge, all three rooted orbit sizes, and the full intersection array
`{4,3,3;1,1,2}` are now available here.  The spectral certificate gives the
sharp fifteen-point coclique bound and its equality case; every graph edge has
an intrinsic, unique fifteen-point edge star, and equality classes of these
stars form a seven-element type.  Conjugation acts transitively and faithfully
on those classes, and a class stabilizer gives the required index-seven
subgroup.
-/
