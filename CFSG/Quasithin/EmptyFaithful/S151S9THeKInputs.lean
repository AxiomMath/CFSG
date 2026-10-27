module

public import CFSG.Quasithin.EmptyFaithful.S151S9THeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeKInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He

@[expose] def heCheckK : Prop :=
  heWit1.Ok 8330 ptAct heDelta heMemW (heSLPC[170]!) ∧ heWit9.Ok 8330 ptAct heDelta heMemW

end CFSG.Quasithin.S151S9T
