module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

instance cube_moduleFinite : Module.Finite K (Cube K) := Module.Finite.of_basis (cubeBasis K)

end CFSG.RankThree.GF2n.Smith81.A5Cube
