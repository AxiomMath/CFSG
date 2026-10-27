module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.Background.HSporLatInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat

@[expose] def m12Wit : Idx3Wit where
  p := 2
  xw := [3, 1]
  rw := [[], [1], [2, 0], [0, 2], [0, 0]]
  ri := [[], [1], [1, 2, 0, 1], [1, 0, 2, 1], [1, 0, 0, 1]]
  czv := [true, true, false]

@[expose] def m12Check : Prop :=
  m12Wit.Ok 12 (codeSetAct 12) m12Delta m12Lat m12SLP[153]!

instance : Decidable m12Check := by
  unfold m12Check
  infer_instance

end CFSG.Quasithin.S151S9T
