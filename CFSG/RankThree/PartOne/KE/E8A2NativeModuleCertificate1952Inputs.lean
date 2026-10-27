module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise

@[expose] def e8Index (i : Fin 8) : Fin Tag.E8.rank := i

@[expose] def e8RootVec (m : Fin 240) : Fin Tag.E8.rank → ℤ := e8Certificate.root m

@[expose] def e8chain13 : Fin 2 → Fin Tag.E8.rank := ![e8Index 0, e8Index 2]

@[expose] def e8a2Weight : Fin 3 → Fin Tag.E8.rank → ℤ :=
  (![![1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]] :
    Fin 3 → Fin 8 → ℤ)

end CFSG.RankThree.PartOne.KE
