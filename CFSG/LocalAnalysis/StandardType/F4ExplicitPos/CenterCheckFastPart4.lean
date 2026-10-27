module

public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Chevalley.RootOps.Sparse
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps3
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps5
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps6
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastSteps7

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterCheckFast
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
variable (L : Type) [Field L]
variable {L}

def f4Steps : List (ℕ × ℕ × ℕ × ℕ) :=
  f4StepsChunk1 ++ f4StepsChunk2 ++ f4StepsChunk3 ++ f4StepsChunk4 ++ f4StepsChunk5 ++
    f4StepsChunk6 ++ f4StepsChunk7

end CFSG.StandardType.F4ExplicitPos.CenterCheckFast
end

end
