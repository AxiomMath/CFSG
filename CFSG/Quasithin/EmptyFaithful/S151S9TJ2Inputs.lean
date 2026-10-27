module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.E2P.SporB.J2Lat

@[expose] def j2Wit : Idx3Wit where
  p := 4
  xw := [3, 0]
  rw := [[], [1], [2, 0], [2, 2], [0, 2]]
  ri := [[], [1], [2, 0], [0, 2, 2, 0], [0, 2]]
  czv := [true, true, false, true, false]

@[expose] def j2Check : Prop := j2Wit.Ok 315 (codeSetAct 315) j2Delta j2Lat j2SLP[143]!

instance : Decidable j2Check := by
  unfold j2Check
  infer_instance

end CFSG.Quasithin.S151S9T
