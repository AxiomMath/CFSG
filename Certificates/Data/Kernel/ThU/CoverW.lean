module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataTh
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.KC.ThU

open CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] def thUCoverW : List (List (Fin 3 × Bool)) :=
  coverWords thULocal3.rels (fun i => [(i, true)]) ++ cubeWords thULocal3.rels ++
    powWords (fun i => thULocal3.ords.getD i 0)

end CFSG.KC.ThU

end
