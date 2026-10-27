module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverInputs
public import CFSG.Sporadic.J3.Group
public import Certificates.Data.CFSGNative.J3.Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover

open CFSG.Sporadic.Bridge.TwoGen
open CFSG.Sporadic.J3 (a b J)
open CFSG.Sporadic.J3.Native (j3Data)

@[expose] noncomputable def ab (i : Fin 2) : J j3Data := img2 (a j3Data) (b j3Data) i.val

@[expose] noncomputable def gen (i : Fin 3) : J j3Data :=
  FreeGroup.lift ab (FreeGroup.mk (genWords.getD i []))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover
